-- Prove2me | solution 1 for TreeStack.stackingCandidate_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:52:20.796034+00:00
-- url     : https://prove2.me/submissions/ed7e836b-bc34-41a4-8c64-005b0b0c326c

import Mathlib
import Definitions.Def_TreeStack_UpperBound
import Definitions.Def_TreeStack_Stacking
import Theorems.Thm_TreeStack_estim_stackingCandidate

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    [Nontrivial V] (T : FiniteTree V) :
    Set.Nonempty {t : ℕ | StackingCandidate T t} :=
  ⟨estim T, estim_stackingCandidate T⟩
end TreeStack
