#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Argument.h"
#include "llvm/Module.h"
#include "llvm/Constants.h"
#include "llvm/Instructions.h"
#include "llvm/LLVMContext.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <map>

using namespace llvm;

struct ABC3 : public ModulePass 
{
	static char ID; // Pass identification, replacement for typeid
	ABC3() : ModulePass(ID) {}
	
	//create C and active as global variables
	struct triplet_{
	  node a;
	  node b;
	  int red;
	};
	
	typedef struct triplet_ triplet;
	
	std::map<triplet,int> *C; 
	std::map<node,int> *active;
	
  bool demandProve(Graph G, index t)
  {
    //initialize C and active
    C = new std::map<triplet,int>();
    active = new std::map<node,int>();
    
    if(prove(a,b,c))
    {
      return true;
    }
    return false
  }
  
  int prove(node a, node b, int c)
  {
    triplet t = new triplet();
    t.a = a; t.b = b; t.red = 2;
    std::map<triplet,int>::iterator it = C.find(t);
    //same or stronger difference was already proven
    if(it != C.end() && c >= it->second) return 2;
    t.red = 0;
    it = C.find(t);
    //same or weaker difference was already disproved
    if(it != C.end() && c <= it->second) return 0;
    t.red = 1;
    it = C.find(t);
    //b is on a cycle that was reduced for same or stronger difference
    if(it != C.end() && c >= it->second) return 1;
    //traversal reached the source vertex, success if a-a<=c
    if(b == a && c >= 0) return 2;
    //if no constraint exists on the value of b, we fail
    if(!b.predecessor()) return 0;
    std::map<node,int>::iterator ait = active.find(b);
    //a cycle was encountered
    if(ait != active.end())
    {
      if(c > active[b]) return 0; //an amplifying cycle
      return 1;                 //a "harmless" cycle
    } 
    int ret;
    active[b] = c;
    if(b.phiNode())
    {
      ret = 2;
      for(node itt = b.pred(); itt!=NULL; itt->next())
      {
        int res = prove(a,itt,c-weight(u,b));
        ret = res < ret ? res : ret;
      }
      if(ret == 0)
      {
        t.red = 0;
        it = C.find(t);
        if(it == C.end()) C[t] = c;
        else if(c > it->second) C[t] = c;
      }
      else if(ret == 1)
      {
        t.red = 0;
        it = C.find(t);
        if(it == C.end() || (it != C.end() && c < it->second))
        {
          t.red = 1;
          it = C.find(t);
          if(it == C.end()) C[t] = c;
          else if(c < it->second) C[t] = c;
        }
      }
      else if(ret == 2)
      {
        t.red = 0;
        it = C.find(t);
        if(it == C.end() || (it != C.end() && c < it->second))
        {
          t.red = 1;
          it = C.find(t);
          if(it == C.end() || (it != C.end() && c > it->second))
          {
            t.red = 2;
            it = C.find(t);
            if(it == C.end()) C[t] = c;
            else if(c < it->second) C[t] = c;
          }
        }
      }
    }
    else
    {
      ret = 0;
      for(node itt = b.pred(); itt!=NULL; itt->next())
      {
        int res = prove(a,itt,c-weight(u,b));
        ret = res > ret ? res : ret;
      }
      if(ret == 2)
      {
        t.red = 2;
        it = C.find(t);
        if(it == C.end()) C[t] = c;
        else if(c < it->second) C[t] = c;
      }
      else if(ret == 1)
      {
        t.red = 2;
        it = C.find(t);
        if(it == C.end() || (it != C.end() && c > it->second))
        {
          t.red = 1;
          it = C.find(t);
          if(it == C.end()) C[t] = c;
          else if(c < it->second) C[t] = c;
        }
      }
      else if(ret == 0)
      {
        t.red = 2;
        it = C.find(t);
        if(it == C.end() || (it != C.end() && c > it->second))
        {
          t.red = 1;
          it = C.find(t);
          if(it == C.end() || (it != C.end() && c > it->second))
          {
            t.red = 0;
            it = C.find(t);
            if(it == C.end()) C[t] = c;
            else if(c > it->second) C[t] = c;
          }
        }
      }
    }
    active.erase(b);
    return ret;
  }

	virtual bool runOnModule(Module &M) {

    return true;
	}
};


char ABC3::ID = 0;
static RegisterPass<ABC3> ABC3("abc3", "auto bounds check");
