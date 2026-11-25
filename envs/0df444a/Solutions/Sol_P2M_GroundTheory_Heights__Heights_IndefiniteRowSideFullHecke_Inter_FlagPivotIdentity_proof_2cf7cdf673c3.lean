-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_proof_2cf7cdf673c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:48.335165+00:00
-- url     : https://prove2.me/submissions/006174a3-adfa-4985-98df-1d595b7e45a9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagPivotIdentity
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_pivotMatrix_rows_ddb0ef3043fc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_pivotCoeff_isLowerTriangular_590a0a974c04
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_pivotCoeff_diag_fb5ec8ecbf02
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_leadMinor_eq_2edbb2d2f46c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_leadDet_zero_8a78e57fd74a

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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagPivotIdentity
variable {R : Type} [CommRing R] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagPivotIdentity
theorem _root_.solution : FlagPivotIdentity.Statement := by
  intro R _ n M j S
  have hP : flagMinor (pivotMatrix M) j S =
      (∏ k ∈ Finset.range j, leadDet M (k + 1)) * flagMinor M j S := by
    unfold flagMinor
    rw [pivotMatrix_rows, Matrix.det_mul,
      Matrix.det_of_isLowerTriangular _ (pivotCoeff_isLowerTriangular M j)]
    simp only [pivotCoeff_diag]
    rw [Fin.prod_univ_eq_prod_range (fun k => leadDet M k), Finset.prod_range_succ', leadDet_zero, mul_one]
  have hI : ∏ a ∈ Finset.Iic j, leadMinor M a = ∏ k ∈ Finset.range (j + 1), leadDet M (k + 1) := by
    simp only [leadMinor_eq]
    have e := Finset.prod_map (Finset.Iic j) Fin.valEmbedding (fun k => leadDet M (k + 1))
    rw [Fin.map_valEmbedding_Iic] at e
    rw [← show (Finset.Iic (j : ℕ)) = Finset.range (j + 1) by ext; simp, e]
    rfl
  rw [hP, hI, Finset.prod_range_succ, leadMinor_eq]
  ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagPivotIdentity
