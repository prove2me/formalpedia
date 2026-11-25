-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_closedBall_7c5ce7e9c022
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:16.194155+00:00
-- url     : https://prove2.me/submissions/b5e9809e-0c36-44c1-8242-5dd27bc181cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly

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
open MeasureTheory Set MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {ι : Type*}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution (r : ℝ) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖) (Metric.closedBall 0 r) := by
  rw [← integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
  have e : (Metric.closedBall (0 : ℂ) r).indicator (fun z : ℂ => Real.log ‖z‖) =
      fun z => (Iic r).indicator Real.log ‖z‖ := by
    funext z
    simp [Set.indicator, Metric.mem_closedBall, dist_zero_right]
  rw [e, integrable_fun_norm_addHaar volume, Complex.finrank_real_complex]
  have e2 : (fun y : ℝ => y ^ (2 - 1) • (Iic r).indicator Real.log y) =
      (Iic r).indicator (fun y => y * Real.log y) := by
    funext y
    by_cases h : y ∈ Iic r <;> simp [Set.indicator, h]
  rw [e2, IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iic]
  exact (Real.continuous_mul_log.integrableOn_Icc (a := 0) (b := r)).mono_set
    (fun y hy => ⟨le_of_lt hy.2, hy.1⟩)
end GroundTheory.Heights₂.Heights.LogInt
