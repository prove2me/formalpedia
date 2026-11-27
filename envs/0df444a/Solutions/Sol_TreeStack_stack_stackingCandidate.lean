-- Prove2me | solution 1 for TreeStack.stack_stackingCandidate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:53:59.547311+00:00
-- url     : https://prove2.me/submissions/61e16b4f-c294-43ee-8bb4-1648239e6d3a

import Mathlib
import Definitions.Def_TreeStack_UpperBound
import Definitions.Def_TreeStack_Stacking
import Theorems.Thm_TreeStack_stackingCandidate_nonempty

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    [Nontrivial V] (T : FiniteTree V) :
    StackingCandidate T (stack T) := by
  unfold stack
  exact Nat.sInf_mem (stackingCandidate_nonempty T)
end TreeStack
