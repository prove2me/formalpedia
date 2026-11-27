-- Prove2me | solution 1 for TreeStack.mass_add_one_le_estim_of_all_scores_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:43:22.627593+00:00
-- url     : https://prove2.me/submissions/5f55d511-56a6-4d11-a93c-5d21ac2429b1

import Mathlib
import Definitions.Def_TreeStack_Consolidation
import Definitions.Def_TreeStack_UpperBound
import Theorems.Thm_TreeStack_OrientedBranch_exists_root_auxCompactPotential_le_rootEstimate_sub_one
import Theorems.Thm_TreeStack_exists_pos_of_mass_pos
import Theorems.Thm_TreeStack_OrientedBranch_mass_le_auxCompactPotential
import Theorems.Thm_TreeStack_card_add_one_le_estim
import Theorems.Thm_TreeStack_rootEstimate_le_estim


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    [Nontrivial V]
    (T : FiniteTree V) (C : Configuration V)
    (hScores : ∀ v, score T C v ≤ 0) :
    mass C + 1 ≤ estim T := by
  by_cases hMassZero : mass C = 0
  · rw [hMassZero]
    have hEstim := card_add_one_le_estim T
    omega
  · have hMassPos : 0 < mass C :=
      Nat.pos_of_ne_zero hMassZero
    rcases exists_pos_of_mass_pos C hMassPos with
      ⟨ambientRoot, hRootPos⟩
    have hMassCompact :=
      OrientedBranch.mass_le_auxCompactPotential
        C ambientRoot hRootPos hScores
    rcases
        OrientedBranch.exists_root_auxCompactPotential_le_rootEstimate_sub_one
          C ambientRoot hScores with
      ⟨r, hCompactRoot⟩
    have hRootEstim := rootEstimate_le_estim T r
    have hRootEstimInt :
        (rootEstimate T r : ℤ) ≤ (estim T : ℤ) := by
      exact_mod_cast hRootEstim
    have hMassEstimInt :
        (mass C : ℤ) + 1 ≤ (estim T : ℤ) := by
      linarith
    exact_mod_cast hMassEstimInt
end TreeStack
