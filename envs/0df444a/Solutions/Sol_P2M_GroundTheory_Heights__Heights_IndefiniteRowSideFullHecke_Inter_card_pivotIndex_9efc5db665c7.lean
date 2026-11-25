-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_card_pivotIndex_9efc5db665c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:44:46.080259+00:00
-- url     : https://prove2.me/submissions/69477a68-d732-491d-ae06-08ff456da56a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_card_pivotCols_ge_41d353af8778

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (n : ℕ) :
    Fintype.card (Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b}) = flagDim n + (n - 1) := by
  rw [Fintype.card_sigma]
  simp_rw [card_pivotCols_ge]
  rw [Fin.sum_univ_eq_sum_range (fun i => n - i) (n - 1)]
  rcases n with _ | m
  · simp [flagDim]
  · simp only [Nat.add_sub_cancel, flagDim]
    have hr : ∑ i ∈ Finset.range m, (m + 1 - i) = ∑ i ∈ Finset.range m, (i + 2) := by
      rw [← Finset.sum_range_reflect (fun i => i + 2) m]
      exact Finset.sum_congr rfl fun i hi => by simp at hi; omega
    rw [hr, Finset.sum_add_distrib]
    have h2 := Finset.sum_range_id_mul_two m
    have h3 : (m + 1) * m = (∑ i ∈ Finset.range m, i) * 2 + 2 * m := by
      rw [h2]; rcases m with _ | k
      · simp
      · simp only [Nat.add_sub_cancel]; ring
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [h3]
    omega
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
