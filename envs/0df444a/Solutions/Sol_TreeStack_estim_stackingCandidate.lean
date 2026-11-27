-- Prove2me | solution 1 for TreeStack.estim_stackingCandidate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:50:33.989888+00:00
-- url     : https://prove2.me/submissions/cead20ee-b429-4518-91b0-a15b8ddd81d1

import Mathlib
import Definitions.Def_TreeStack_UpperBound
import Definitions.Def_TreeStack_Stacking
import Theorems.Thm_TreeStack_card_add_one_le_estim
import Theorems.Thm_TreeStack_universalStackable_estim


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    [Nontrivial V] (T : FiniteTree V) :
    StackingCandidate T (estim T) := by
  constructor
  · have hcard : 1 < Fintype.card V :=
      Fintype.one_lt_card
    have hEstim := card_add_one_le_estim T
    omega
  · exact universalStackable_estim T
end TreeStack
