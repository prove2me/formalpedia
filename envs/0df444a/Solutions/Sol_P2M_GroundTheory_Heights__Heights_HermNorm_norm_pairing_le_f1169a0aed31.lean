-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermNorm_norm_pairing_le_f1169a0aed31
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:54:44.899661+00:00
-- url     : https://prove2.me/submissions/dc000513-e60d-4cd0-a224-fd472e362386

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
theorem _root_.solution (h : HermNorm n) (u y : Fin n → ℂ) :
    ‖∑ j, u j * y j‖ ≤ h.norm u * h.dualNorm y := by
  have hinv : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  have hpair : ∑ j, u j * y j = ∑ i, (h.mat *ᵥ u) i * ((h.matᵀ)⁻¹ *ᵥ y) i := by
    have e1 : (∑ j, u j * y j) = u ⬝ᵥ y := rfl
    have e2 : (∑ i, (h.mat *ᵥ u) i * ((h.matᵀ)⁻¹ *ᵥ y) i) = (h.mat *ᵥ u) ⬝ᵥ ((h.matᵀ)⁻¹ *ᵥ y) := rfl
    rw [e1, e2, dotProduct_comm (h.mat *ᵥ u), dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec,
      mul_nonsing_inv _ hinv, one_mulVec, dotProduct_comm]
  rw [hpair]
  calc ‖∑ i, (h.mat *ᵥ u) i * ((h.matᵀ)⁻¹ *ᵥ y) i‖
      ≤ ∑ i, ‖(h.mat *ᵥ u) i‖ * ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ ≤ √(∑ i, ‖(h.mat *ᵥ u) i‖ ^ 2) * √(∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = h.norm u * h.dualNorm y := rfl
end HermNorm
end GroundTheory.Heights₂.Heights
