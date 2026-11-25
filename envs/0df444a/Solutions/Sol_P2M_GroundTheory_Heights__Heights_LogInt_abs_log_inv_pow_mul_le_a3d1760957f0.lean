-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_abs_log_inv_pow_mul_le_a3d1760957f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:05.530037+00:00
-- url     : https://prove2.me/submissions/584de57d-4a20-412a-91a3-e79967fa17de

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere

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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution (N : ℝ) (hN : 0 ≤ N) (d : ℕ) (x : ℂ) :
    |Real.log ‖((N : ℂ)⁻¹) ^ d * x‖| ≤ d * |Real.log N| + |Real.log ‖x‖| := by
  have hnn : 0 ≤ (d : ℝ) * |Real.log N| + |Real.log ‖x‖| := by positivity
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN]
  by_cases h0 : (N⁻¹) ^ d * ‖x‖ = 0
  · rw [h0, Real.log_zero, abs_zero]; exact hnn
  · rw [Real.log_mul (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0), Real.log_pow, Real.log_inv]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_mul, Nat.abs_cast, abs_neg]
end GroundTheory.Heights₂.Heights.LogInt
