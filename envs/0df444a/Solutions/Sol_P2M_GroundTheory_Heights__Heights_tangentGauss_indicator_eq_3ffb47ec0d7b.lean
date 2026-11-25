-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_tangentGauss_indicator_eq_3ffb47ec0d7b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:42:06.941816+00:00
-- url     : https://prove2.me/submissions/f40b1fa5-ccc2-4f40-8822-d872225c0d93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadPlaneJac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussMoment
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linProj_smul_left_0afd722762be

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
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m n : ℕ} (π : Fin m → Fin n → ℂ) (r : ℝ) :
    (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π ((r : ℂ) • firstCoordVec n)) =
      if |r| * ‖linProj π (firstCoordVec n)‖ < 1 then (1 : ℝ≥0∞) else 0 := by
  simp only [Set.indicator, Metric.mem_ball, dist_zero_right, linProj_smul_left, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, Pi.one_apply]
end GroundTheory.Heights₂.Heights
