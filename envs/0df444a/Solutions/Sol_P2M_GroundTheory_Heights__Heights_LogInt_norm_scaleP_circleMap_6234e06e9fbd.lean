-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_norm_scaleP_circleMap_6234e06e9fbd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:35.212577+00:00
-- url     : https://prove2.me/submissions/a90ebfe4-435a-4520-a3c4-6e8dfed9e442

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
theorem _root_.solution (p : ι → Prop) [DecidablePred p] (θ : ℝ) (u : ι → ℂ) (x : ι) :
    ‖scaleP p (circleMap 0 1 θ) u x‖ = ‖u x‖ := by
  by_cases h : p x <;> simp [scaleP, h]
end GroundTheory.Heights₂.Heights.LogInt
