#define AFL_LLVM_PASS

#include "config.h"
#include "debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <sys/time.h>

#include <list>
#include <string>
#include <fstream>
#include <set>

#include "llvm/Config/llvm-config.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemorySSAUpdater.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Pass.h"
#include "llvm/IR/Constants.h"

#include "afl-llvm-common.h"

#define ENABLE_TRYY 1
#define ENABLE_ROR 1

using namespace llvm;
using namespace std;
using xyz = std::array<int, 3>;
using cur_pre = std::array<uint32_t, 2>;

namespace {

#if ENABLE_ROR
uint32_t ROR(uint32_t target, uint32_t shift_bits) {
  //return target >> shift_bits;
  uint32_t value = target;
  for(uint32_t i = 0; i < shift_bits; i++){
    if(value & 1)
      value = ((value >> 1) | 1 << (MAP_SIZE_POW2 - 1));
    else
      value = value >> 1;
  }
  return value;
};
#endif

class AFLLTOPass : public ModulePass {

public:
  static char ID;

  AFLLTOPass() : ModulePass(ID) {

    char *ptr;

    if (getenv("AFL_DEBUG")) debug = 1;
    if ((ptr = getenv("AFL_LLVM_LTO_STARTID")) != NULL)
      if ((afl_global_id = atoi(ptr)) < 0 || afl_global_id >= MAP_SIZE)
        FATAL("AFL_LLVM_LTO_STARTID value of \"%s\" is not between 0 and %d\n",
              ptr, MAP_SIZE - 1);

    skip_nozero = getenv("AFL_LLVM_SKIP_NEVERZERO");

  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {

    ModulePass::getAnalysisUsage(AU);
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();

  }

  bool runOnModule(Module &M) override;

protected:
  uint32_t afl_global_id = 1;
  char * skip_nozero = NULL;

  set<uint32_t> idHashSet, tmpHashSet;

  vector<BasicBlock *> singleBBs, multiBBs, solvBBs, unsolvBBs;
  map<BasicBlock *, vector< BasicBlock* > > predMap;
  map<BasicBlock *, uint32_t> BBIdMap;

  map<BasicBlock *, xyz> fmulMap;
  map<cur_pre, uint32_t> fhashMap;
  map<uint32_t, uint32_t> fsingleMap;

  bool disjoint(set<uint32_t>& tmpHashSet, set<uint32_t>& idHashSet)  {
    // We can do this because C++ set class is based on RB tree and thus elements are ordered.
    set<uint32_t>::iterator it = tmpHashSet.begin();
    set<uint32_t>::iterator ie = tmpHashSet.end();
    set<uint32_t>::iterator jt = idHashSet.begin();
    set<uint32_t>::iterator je = idHashSet.end();
    while(it != ie && jt != je){
      if(*it < *jt)
        it++;
      else if(*it > * jt)
        jt++;
      else
        return false;
    }
    return true;
  }
  /* search parameters for blocks with multiple precedents */
  int calcFmul() {
    int Y = 1;
#if ENABLE_TRYY
    double min = 1.0;
    for (int y = 1; y < MAP_SIZE_POW2; y++ ) {
      {
        // make set or map to empty
        idHashSet.clear();
        fmulMap.clear();
        solvBBs.clear();
        unsolvBBs.clear();
        for (auto BB : multiBBs) {
          bool solved = false;
          // search parameters for BB
          for (int x = 1; x < MAP_SIZE_POW2; x++ ) {
            for (int z = 1; z < MAP_SIZE_POW2; z++ ) {
              tmpHashSet.clear();
              auto cur_loc = BBIdMap[BB];
              // idHashSet for all incoming edges
              for (auto prevBB : predMap[BB]) {
#if ENABLE_ROR
                auto edgeHash = ROR(BBIdMap[prevBB], y) ^ ROR(cur_loc, x) + z;
#else
                auto edgeHash = (BBIdMap[prevBB] >> y) ^ (cur_loc >> x) + z;
#endif
                tmpHashSet.insert(edgeHash);
              }
              // find a solution for BB if no collision
              if (tmpHashSet.size() == predMap[BB].size() && disjoint(tmpHashSet, idHashSet)) {
                solved = true;
                fmulMap[BB] = xyz({x, y, z});
                idHashSet.insert(tmpHashSet.begin(), tmpHashSet.end());
                goto early_succeed1;
              }
            }
          }
          early_succeed1:
          if(solved)
            solvBBs.push_back(BB);
          else
            unsolvBBs.push_back(BB);
        }
      }
      auto sizeofSolv = solvBBs.size();
      auto sizeofUnsolv = unsolvBBs.size();
      auto cur = ((double)sizeofUnsolv) / ( sizeofUnsolv + sizeofSolv);
      if (cur < min) {
        min = cur;
        Y = y;
      }
      errs() << "trying y: " << y << " solved: " << sizeofSolv << " unsolved: " << sizeofUnsolv << '\n';
      if(min == 0)
        break;
    }
    errs() << "Minimum unsolved：" << (unsigned int)(min * 100) << "% with Y choosen:" << Y << '\n';
#endif
    {
      //make set or map to empty
      idHashSet.clear();
      fmulMap.clear();
      solvBBs.clear();
      unsolvBBs.clear();
      for (auto BB : multiBBs) {
        bool solved = false;
        // search parameters for BB
        for (int x = 1; x < MAP_SIZE_POW2; x++ ) {
          for (int z = 1; z < MAP_SIZE_POW2; z++ ) {
            tmpHashSet.clear();
            auto cur_loc = BBIdMap[BB];
            // idHashSet for all incoming edges
            for (auto prevBB : predMap[BB]) {
#if ENABLE_ROR
              auto edgeHash = ROR(BBIdMap[prevBB], Y) ^ ROR(cur_loc, x) + z;
#else
              auto edgeHash = (BBIdMap[prevBB] >> Y) ^ (cur_loc >> x) + z;
#endif
              tmpHashSet.insert(edgeHash);
            }
            // find a solution for BB if no collision
            if (tmpHashSet.size() == predMap[BB].size() && disjoint(tmpHashSet, idHashSet)) {
              solved = true;
              fmulMap[BB] = xyz({x, Y, z});
              idHashSet.insert(tmpHashSet.begin(), tmpHashSet.end());
              goto early_succeed2;
            }
          }
        }
        early_succeed2:
        if(solved)
          solvBBs.push_back(BB);
        else
          unsolvBBs.push_back(BB);
        }
      }
    return Y;
  }
  /* build the hash table for unsolvable blocksUnsol */
  void calcFhash() {
    fhashMap.clear();
    for (auto BB : unsolvBBs) {
      bool ok =false;
      auto cur_loc = BBIdMap[BB];
      for (auto prevBB : predMap[BB]) {
        auto prev_loc = BBIdMap[prevBB];
        for (int i = 0; i < MAP_SIZE; i++) {
          //errs() << idHashSet.size() << '\n';
          if (!idHashSet.count(i)) {
            fhashMap[cur_pre({cur_loc, prev_loc})] = i;
            idHashSet.insert(i);
            ok = true;
            break;
          }
        }
      }
      if(!ok) {
        errs() << "calcFhash failed because of bitmap capacity." << '\n';
        exit(1);
      }
    }
  }
  /* build the hash table for blocks with single precedent */
  void calcSingle() {
    fsingleMap.clear();
    for (auto BB : singleBBs) {
      auto cur_loc = BBIdMap[BB];
        bool ok = false;
        for (int i = 0; i < MAP_SIZE; i++) {
          if (!idHashSet.count(i)) {
            fsingleMap[cur_loc] = i;
            idHashSet.insert(i);
            ok = true;
            break;
          }
        }
        if (!ok) {
          errs() << "calcSingle failed because of bitmap capacity." << '\n';
          exit(2);
        }
    }
  }
};
}// namespace

bool AFLLTOPass::runOnModule(Module &M) {
  LLVMContext &C = M.getContext();
  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */
  char be_quiet = 0;
  if (isatty(2) && !getenv("AFL_QUIET")) {
    SAYF(cCYA "afl-llvm-lto-pass CollAFL++ " cBRI VERSION cRST " by <dwfault@163.com>\n");
  }
  else
    be_quiet = 1;

  /* Decide instrumentation ratio */
  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;
  if (inst_ratio_str) {
    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");
  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */
  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                          GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");
  GlobalVariable *AFLPrevLocPtrTls =
      new GlobalVariable(M, Int32Ty, false,
                          GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
                          0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  /* Count all the things! */
  int inst_blocks = 0;
  uint32_t counter = afl_global_id;
  for (auto &F : M) {
    if (isIgnoreFunction(&F))
      continue;

    for (Function::iterator b = F.begin(), be = F.end(); b != be; ++b) {
      BasicBlock* BB = &*b;

      if(BB->hasNPredecessors(0))
        continue;

      if(BB->hasNPredecessors(1)){
        singleBBs.push_back(BB);
      }
      else {
        multiBBs.push_back(BB);
      }
      for (const auto &pred : predecessors(BB)){
        predMap[BB].push_back(pred);
      }
      if (AFL_R(100) >= inst_ratio)
        continue;

      /* Make up counter */
      BBIdMap[BB] = counter++;
    }
  }
  errs() << "singleBBs size: " << singleBBs.size() << '\n';
  errs() << "multiBBs size: " << multiBBs.size() << '\n';
  int Y = calcFmul();
  calcFhash();
  calcSingle();
  errs() << "BBIdMap size: " << BBIdMap.size() << '\n';
  errs() << "predMap size: " << predMap.size() << '\n';

  errs() << "fsingleMap size: " << fsingleMap.size() << '\n';
  errs() << "fmulMap size: " << fmulMap.size() << '\n';
  errs() << "\tsolvBBs size: " << solvBBs.size() << '\n';
  errs() << "\tunsolvBBs size: " << unsolvBBs.size() << '\n';
  errs() << "fhashMap size: " << fhashMap.size() << '\n';

  auto totalAtMost = fsingleMap.size() + fmulMap.size() + fhashMap.size();
  errs() << "Total edges instrumented at most: fsingleMap size + fmulMap size + fhashMap size == " <<  totalAtMost  << '\n';

  for (auto &F : M) {
    if (isIgnoreFunction(&F))
      continue;

    for (Function::iterator b = F.begin(), be = F.end(); b != be; ++b) {
      BasicBlock* BB = &*b;

      if(BB->hasNPredecessors(0) || !BBIdMap.count(BB))
        continue;
      if(BB->hasNPredecessors(1)){
        continue;
      }
      else {
        if(!fmulMap.count(BB)) {
          continue;
        }
        else {
          // Solved using fmulMap
          BasicBlock::iterator IP = BB->getFirstInsertionPt();
          IRBuilder<> IRB(&(*IP));

          // Load Previous BB id
          LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLocPtrTls);
          PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
          Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, Int32Ty);

          //We have Current BB id
          auto cur_loc = BBIdMap[BB];

          // Load __afl_area_ptr
          LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
          MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

          // Calculate Edge id
          auto XYZ = fmulMap[BB];
          int X = XYZ[0];
          int Y = XYZ[1];
          int Z = XYZ[2];
#if ENABLE_ROR
          auto XorCurPre = IRB.CreateXor(ConstantInt::get(Int32Ty, ROR(cur_loc, X)), PrevLocCasted);
#else
          auto XorCurPre = IRB.CreateXor(ConstantInt::get(Int32Ty, (cur_loc >> X)), PrevLocCasted);
#endif
          auto XorPlusZ = IRB.CreateAdd(XorCurPre, ConstantInt::get(Int32Ty, Z));
          Value * XorPlusZCasted = IRB.CreateZExt(XorPlusZ, Int32Ty);
          Value * MapPtrIdx = IRB.CreateGEP(MapPtr, XorPlusZCasted);

          // Update bitmap
          LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
          Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
          Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
          IRB.CreateStore(Incr, MapPtrIdx)->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

          // Set prev_loc to cur_loc >> Y
#if ENABLE_ROR
          //errs() << ' ' << cur_loc << ' ' << Y << ' ' <<  ROR(cur_loc, Y) <<'\n';
          StoreInst *Store = IRB.CreateStore(ConstantInt::get(Int32Ty, ROR(cur_loc, Y)), AFLPrevLocPtrTls);
#else
          StoreInst *Store = IRB.CreateStore(ConstantInt::get(Int32Ty, (cur_loc >> Y)), AFLPrevLocPtrTls);
#endif
          Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

          // Update counter
          inst_blocks++;
        }
      }
    }

    for (Function::iterator b = F.begin(), be = F.end(); b != be; ++b) {
      BasicBlock* BB = &*b;

      if(BB->hasNPredecessors(0) || !BBIdMap.count(BB))
        continue;
      if(BB->hasNPredecessors(1)){
        continue;
      }
      else {
        if(fmulMap.count(BB)) {
          continue;
        }
        else {
          // Unsolved using fhashMap
          auto cur_loc = BBIdMap[BB];
          if(cur_loc) {
            for(auto prevBB : predMap[BB]) {
              auto prev_loc = BBIdMap[prevBB];

              if(fhashMap.count(cur_pre({cur_loc, prev_loc}))) {

                std::vector<BasicBlock *> Successors;
                for (succ_iterator SI = succ_begin(prevBB), SE = succ_end(prevBB); SI != SE; SI++) {
                  Successors.push_back(*SI);
                }

                BasicBlock * dummyBB = NULL;
                for(BasicBlock * IBB : Successors) {

                  dummyBB = SplitEdge(prevBB, IBB);
                  if (IBB != BB) {
                  }
                  else {
                    BasicBlock::iterator IP = dummyBB->getFirstInsertionPt();
                    IRBuilder<> IRB(&(*IP));

                    // Load __afl_area_ptr
                    LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
                    MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

                    // Calculate Edge id
                    ConstantInt *Edge = ConstantInt::get(Int32Ty, fhashMap[cur_pre({cur_loc, prev_loc})]);
                    Value * MapPtrIdx = IRB.CreateGEP(MapPtr, Edge);

                    // Update bitmap
                    LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
                    Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
                    Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
                    IRB.CreateStore(Incr, MapPtrIdx)->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

                    // Set prev_loc as cur_loc >> Y
#if ENABLE_ROR
                    //errs() << ' ' << cur_loc << ' ' << Y << ' ' <<  ROR(cur_loc, Y) <<'\n';
                    StoreInst *Store = IRB.CreateStore(ConstantInt::get(Int32Ty, ROR(cur_loc, Y)), AFLPrevLocPtrTls);
#else
                    StoreInst *Store = IRB.CreateStore(ConstantInt::get(Int32Ty, (cur_loc >> Y)), AFLPrevLocPtrTls);
#endif
                    Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

                    // Update counter
                    inst_blocks++;
                  }
                }
              }
            }
          }
        }
      }
    }

    for (Function::iterator b = F.begin(), be = F.end(); b != be; ++b) {
      BasicBlock* BB = &*b;

      if(BB->hasNPredecessors(0) || !BBIdMap.count(BB))
        continue;

      if(fsingleMap.count(BBIdMap[BB])) {

        // In some senerios, when a BB is instrumented using fmulMap or fhashMap, it could be also an BB
        // with single predecessor. Thus this BB would be instrumented twice.
        // This is acceptable and need not to be dealt with. Otherwise things will become a little bit complicated.
        //if(BB is previously instrumented)
        //  continue;

        // fsingleMap
        BasicBlock::iterator IP = BB->getFirstInsertionPt();
        IRBuilder<> IRB(&(*IP));

        // We have Current BB id
        auto cur_loc = BBIdMap[BB];

        // Load __afl_area_ptr
        LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
        MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

        // Calculate Edge id
        ConstantInt *Edge = ConstantInt::get(Int32Ty, fsingleMap[cur_loc]);
        Value * MapPtrIdx = IRB.CreateGEP(MapPtr, Edge);

        // Update bitmap
        LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
        Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
        IRB.CreateStore(Incr, MapPtrIdx)->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

        // Set prev_loc as cur_loc >> Y
#if ENABLE_ROR
        //errs() << ' ' << cur_loc << ' ' << Y << ' ' <<  ROR(cur_loc, Y) <<'\n';
        StoreInst *Store = IRB.CreateStore(ConstantInt::get(Int32Ty, ROR(cur_loc, Y)), AFLPrevLocPtrTls);
#else
        StoreInst *Store = IRB.CreateStore(ConstantInt::get(Int32Ty, (cur_loc >> Y)), AFLPrevLocPtrTls);
#endif
        Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

        // Update counter
        inst_blocks++;
      }
    }
  }

  /* Say something nice. */
  if (!be_quiet) {
    if (!inst_blocks)
      WARNF("No instrumentation targets found.");
    else
      OKF("Instrumented %u edges with no collisions (on average %llu "
          "collisions would be in afl-gcc/afl-clang-fast)(%s mode, ratio %u%%).",
          inst_blocks, calculateCollisions(inst_blocks),
          getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);
  }

  return true;
}

char AFLLTOPass::ID = 0;

static void registerAFLLTOPass(const PassManagerBuilder &,
                               legacy::PassManagerBase &PM) {

  PM.add(new AFLLTOPass());

}

static RegisterPass<AFLLTOPass> X("afl-lto", "afl++ LTO instrumentation pass",
                                  false, false);

static RegisterStandardPasses RegisterAFLLTOPass(
    PassManagerBuilder::EP_FullLinkTimeOptimizationLast, registerAFLLTOPass);

