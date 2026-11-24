-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_measurable_scaleP_ff4ed9e0e20e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:00.402833+00:00
-- url     : https://prove2.me/submissions/206ba820-c923-472f-8c54-ea56909508f1

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
theorem _root_.solution [Fintype ι] (p : ι → Prop) [DecidablePred p] :
    Measurable (Function.uncurry fun θ : ℝ => scaleP p (circleMap 0 1 θ) : ℝ × (ι → ℂ) → ι → ℂ) := by
  apply Continuous.measurable
  refine continuous_pi fun x => ?_
  by_cases h : p x
  · simp only [Function.uncurry, scaleP, h, if_true]
    exact ((continuous_circleMap 0 1).comp continuous_fst).mul ((continuous_apply x).comp continuous_snd)
  · simp only [Function.uncurry, scaleP, h, if_false]
    exact (continuous_apply x).comp continuous_snd
end GroundTheory.Heights₂.Heights.LogInt
