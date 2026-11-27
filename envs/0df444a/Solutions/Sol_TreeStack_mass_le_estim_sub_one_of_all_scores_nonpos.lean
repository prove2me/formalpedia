-- Prove2me | solution 1 for TreeStack.mass_le_estim_sub_one_of_all_scores_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:45:10.443746+00:00
-- url     : https://prove2.me/submissions/3dde1cac-e837-4677-b348-b44182aad16d

import Mathlib
import Definitions.Def_TreeStack_Consolidation
import Definitions.Def_TreeStack_UpperBound
import Theorems.Thm_TreeStack_mass_add_one_le_estim_of_all_scores_nonpos

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    [Nontrivial V]
    (T : FiniteTree V) (C : Configuration V)
    (hScores : ∀ v, score T C v ≤ 0) :
    mass C ≤ estim T - 1 := by
  have h :=
    mass_add_one_le_estim_of_all_scores_nonpos T C hScores
  omega
end TreeStack
