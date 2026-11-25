-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotMatrix_mem_pivotAlgP_13573ffee2ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:47.788955+00:00
-- url     : https://prove2.me/submissions/c21c9f8d-3106-4990-ae86-8b89437ea0b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotMinor_eq_zero_37c4884a24bb


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
variable (F : Type) [Field F] (n : ℕ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (j : Fin (n - 1)) (r : Fin (j + 1)) (b : Fin n) :
    pivotMatrix (genMat F n) (Fin.castLE (by have := j.2; omega) r) b ∈ pivotAlgP F n := by
  have hr : (r : ℕ) < n - 1 := by have := j.2; have := r.2; omega
  simp only [pivotMatrix, Matrix.of_apply, Fin.val_castLE, dif_pos hr]
  by_cases h : (r : ℕ) ≤ b
  · exact Algebra.subset_adjoin ⟨⟨⟨r, hr⟩, ⟨b, h⟩⟩, rfl⟩
  · rw [pivotMinor_eq_zero _ ⟨r, hr⟩ b (by simp only; omega)]
    exact zero_mem _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
