-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_smul_549dac818b96
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:25:26.596383+00:00
-- url     : https://prove2.me/submissions/737e7af8-551b-4076-9fc1-e3ecb17db5e0

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
open GroundTheory.Heights₂.Heights.HermNorm
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.HermNorm
theorem _root_.solution (h : HermNorm n) (a : ℂ) (v : Fin n → ℂ) :
    h.norm (fun j => a * v j) = ‖a‖ * h.norm v := by
  unfold HermNorm.norm
  have e : (h.mat *ᵥ fun j => a * v j) = fun i => a * (h.mat *ᵥ v) i := by
    have : (fun j => a * v j) = a • v := rfl
    rw [this, Matrix.mulVec_smul]
    rfl
  rw [e]
  simp_rw [norm_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
end GroundTheory.Heights₂.Heights.HermNorm
