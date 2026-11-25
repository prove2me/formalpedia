-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_integral_phaseLaw_dd825db4ed22
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:36.343474+00:00
-- url     : https://prove2.me/submissions/ee876d0c-b093-4f01-8068-db3f2f82bb78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong

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
open MvPolynomial MeasureTheory ProbabilityTheory Real
noncomputable section
open GroundTheory.Heights₂.Heights.PointwiseLelong
variable {N : ℕ}
namespace GroundTheory.Heights₂.Heights.PointwiseLelong
theorem _root_.solution (f : ℝ → ℝ) :
    ∫ θ, f θ ∂phaseLaw = (2 * π)⁻¹ * ∫ θ in -π..π, f θ := by
  rw [phaseLaw, ProbabilityTheory.cond, integral_smul_measure, Real.volume_Ioc,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), smul_eq_mul]
  congr 2
  ring
end GroundTheory.Heights₂.Heights.PointwiseLelong
