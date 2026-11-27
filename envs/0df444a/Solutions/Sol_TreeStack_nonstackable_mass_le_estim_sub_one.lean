-- Prove2me | solution 1 for TreeStack.nonstackable_mass_le_estim_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:47:19.686355+00:00
-- url     : https://prove2.me/submissions/d4186ded-3e93-4426-ac93-6777306daac7

import Mathlib
import Definitions.Def_TreeStack_Consolidation
import Definitions.Def_TreeStack_UpperBound
import Theorems.Thm_TreeStack_mass_le_estim_sub_one_of_all_scores_nonpos
import Theorems.Thm_TreeStack_not_stackable_iff_all_scores_nonpos


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    [Nontrivial V]
    (T : FiniteTree V) (C : Configuration V)
    (hNot : ¬ Stackable T.graph C) :
    mass C ≤ estim T - 1 := by
  exact
    mass_le_estim_sub_one_of_all_scores_nonpos T C
      ((not_stackable_iff_all_scores_nonpos T C).1 hNot)
end TreeStack
