-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_sum_sq_nrmv_le_0587e199c44b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:17:03.546433+00:00
-- url     : https://prove2.me/submissions/e0d6cb28-a389-4362-b16b-af21875118f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSphereMeanLinearBall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_std_norm_dd32b5c030d0

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
open MeasureTheory Set
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMeanLinearBall
namespace GroundTheory.Heights₂.Heights.SphereMeanLinearBall
theorem _root_.solution (n : ℕ) (w : Fin n → ℂ) :
    ∑ j, ‖nrmv (HermNorm.std n) w j‖ ^ 2 ≤ 1 := by
  have hS : 0 ≤ ∑ j, ‖w j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have e : ∀ j, ‖nrmv (HermNorm.std n) w j‖ ^ 2 = (∑ j, ‖w j‖ ^ 2)⁻¹ * ‖w j‖ ^ 2 := by
    intro j
    rw [nrmv, std_norm, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt hS]
  rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum]
  rcases eq_or_ne (∑ j, ‖w j‖ ^ 2) 0 with h | h
  · simp [h]
  · rw [inv_mul_cancel₀ h]
end GroundTheory.Heights₂.Heights.SphereMeanLinearBall
