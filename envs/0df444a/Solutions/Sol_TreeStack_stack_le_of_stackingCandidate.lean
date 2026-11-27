-- Prove2me | solution 1 for TreeStack.stack_le_of_stackingCandidate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:34:06.661002+00:00
-- url     : https://prove2.me/submissions/5a95d699-3a51-4e00-8a3f-28c01e6c7b8a

import Mathlib
import Definitions.Def_TreeStack_UpperBound
import Definitions.Def_TreeStack_Stacking

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    [Nontrivial V] (T : FiniteTree V) {t : ℕ}
    (ht : StackingCandidate T t) :
    stack T ≤ t := by
  unfold stack
  exact Nat.sInf_le ht
end TreeStack
