-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_coord_5e7af9876972
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:41.493178+00:00
-- url     : https://prove2.me/submissions/391c557e-8fe0-47b5-b5cb-78f79a6c44c3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_closedBall_7c5ce7e9c022

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
theorem _root_.solution [Fintype ι] (r : ℝ) (x : ι) :
    IntegrableOn (fun u : ι → ℂ => Real.log ‖u x‖) (polydisc ι r) := by
  have : IsFiniteMeasure ((volume : Measure ℂ).restrict (Metric.closedBall 0 r)) :=
    isFiniteMeasure_restrict.mpr (measure_closedBall_lt_top).ne
  rw [IntegrableOn, polydisc, volume_pi, Measure.restrict_pi_pi]
  exact integrable_comp_eval (μ := fun _ : ι => (volume : Measure ℂ).restrict (Metric.closedBall 0 r))
    (i := x) (integrableOn_log_norm_closedBall r)
end GroundTheory.Heights₂.Heights.LogInt
