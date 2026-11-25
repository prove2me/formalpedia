-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_measurePreserving_scaleP_5f8462bc33f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:39:44.194873+00:00
-- url     : https://prove2.me/submissions/6ac7944d-0dc2-4ade-8714-29ab762ddd07

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurePreserving_mul_circleMap_a47a1e5d7020

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
theorem _root_.solution [Fintype ι] (p : ι → Prop) [DecidablePred p] (θ : ℝ) :
    MeasurePreserving (scaleP p (circleMap 0 1 θ)) volume volume := by
  have := measurePreserving_pi (fun _ : ι => (volume : Measure ℂ)) (fun _ : ι => (volume : Measure ℂ))
    (f := fun x => if p x then (fun z : ℂ => circleMap 0 1 θ * z) else id)
    (fun x => by
      by_cases h : p x
      · simp only [h, if_true]; exact measurePreserving_mul_circleMap θ
      · simp only [h, if_false]; exact MeasurePreserving.id _)
  have e : scaleP p (circleMap 0 1 θ) =
      fun a x => (if p x then (fun z : ℂ => circleMap 0 1 θ * z) else id) (a x) := by
    funext u x
    by_cases h : p x <;> simp [scaleP, h]
  rw [e]
  exact this
end GroundTheory.Heights₂.Heights.LogInt
