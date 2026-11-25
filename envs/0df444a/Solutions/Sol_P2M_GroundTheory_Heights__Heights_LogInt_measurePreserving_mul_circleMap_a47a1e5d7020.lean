-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_measurePreserving_mul_circleMap_a47a1e5d7020
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:26.467801+00:00
-- url     : https://prove2.me/submissions/2d07a3a6-1b0d-40db-81a0-24585ab6894e

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
theorem _root_.solution (θ : ℝ) :
    MeasurePreserving (fun z : ℂ => circleMap 0 1 θ * z) volume volume := by
  have h := (rotation (Circle.exp θ)).measurePreserving
  have e : (fun z : ℂ => circleMap 0 1 θ * z) = rotation (Circle.exp θ) := by
    funext z
    simp [rotation_apply, Circle.coe_exp, circleMap_zero]
  rw [e]
  exact h
end GroundTheory.Heights₂.Heights.LogInt
