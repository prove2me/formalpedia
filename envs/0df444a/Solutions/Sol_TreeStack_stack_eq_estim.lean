-- Prove2me | solution 1 for TreeStack.stack_eq_estim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:56:30.051805+00:00
-- url     : https://prove2.me/submissions/6b52d8f6-925a-4b03-a753-68718c49d800

import Mathlib
import Definitions.Def_TreeStack_UpperBound
import Definitions.Def_TreeStack_Stacking
import Theorems.Thm_TreeStack_estim_stackingCandidate
import Theorems.Thm_TreeStack_stack_stackingCandidate
import Theorems.Thm_TreeStack_stack_le_of_stackingCandidate
import Theorems.Thm_TreeStack_estim_le_of_stackingCandidate

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    [Nontrivial V] (T : FiniteTree V) :
    stack T = estim T := by
  apply Nat.le_antisymm
  · exact stack_le_of_stackingCandidate T (estim_stackingCandidate T)
  · exact estim_le_of_stackingCandidate T (stack_stackingCandidate T)
end TreeStack
