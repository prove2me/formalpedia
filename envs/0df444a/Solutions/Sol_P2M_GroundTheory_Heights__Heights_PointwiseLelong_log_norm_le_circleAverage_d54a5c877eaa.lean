-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_log_norm_le_circleAverage_d54a5c877eaa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:36.946377+00:00
-- url     : https://prove2.me/submissions/52da4ee5-bb4c-4b06-b3f6-a56e45e4cf63

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
theorem _root_.solution {g : ℂ → ℂ} (hg : Differentiable ℂ g) (h0 : g 0 ≠ 0) :
    Real.log ‖g 0‖ ≤ circleAverage (fun z => Real.log ‖g z‖) 0 1 := by
  have han : AnalyticOnNhd ℂ g (Metric.closedBall 0 |1|) := fun z _ => hg.analyticAt z
  rw [han.circleAverage_log_norm one_ne_zero h0]
  refine le_add_of_nonneg_left (finsum_nonneg fun u => ?_)
  by_cases hu : u ∈ Metric.closedBall (0 : ℂ) |1|
  · refine mul_nonneg (by exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg han) u) ?_
    rw [one_mul, zero_sub, norm_neg, Real.log_inv]
    refine neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) ?_)
    simpa using hu
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
    simp
end GroundTheory.Heights₂.Heights.PointwiseLelong
