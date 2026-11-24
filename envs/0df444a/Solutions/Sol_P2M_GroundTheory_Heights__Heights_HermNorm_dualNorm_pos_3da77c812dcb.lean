-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_pos_3da77c812dcb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:22.87572+00:00
-- url     : https://prove2.me/submissions/8352dade-9805-4ff2-a00e-5495426b7b2e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField Matrix
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace HermNorm
theorem _root_.solution (h : HermNorm n) {y : Fin n → ℂ} (hy : y ≠ 0) : 0 < h.dualNorm y := by
  have hinv : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  unfold HermNorm.dualNorm
  apply Real.sqrt_pos.mpr
  have hBy : (h.matᵀ)⁻¹ *ᵥ y ≠ 0 := by
    intro h0
    apply hy
    have := congrArg (fun x => h.matᵀ *ᵥ x) h0
    simp only [mulVec_mulVec, mul_nonsing_inv _ hinv, one_mulVec, mulVec_zero] at this
    exact this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hBy
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by
    have : 0 < ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ := norm_pos_iff.mpr hi
    positivity⟩
end HermNorm
end GroundTheory.Heights₂.Heights
