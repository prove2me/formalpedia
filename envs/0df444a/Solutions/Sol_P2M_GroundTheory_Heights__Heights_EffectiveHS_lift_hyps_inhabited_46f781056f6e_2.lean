-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_hyps_inhabited_46f781056f6e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:54:50.258037+00:00
-- url     : https://prove2.me/submissions/0b6c2915-0a54-452b-87b5-add9ed915192

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision

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
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
open MeasureTheory
namespace GroundTheory.Heights₂.Heights.EffectiveHS
theorem _root_.solution :
    (∀ (i : Fin 1) (x : Unit), ‖(fun _ _ => (1 : ℂ)) i x‖ ≤ (fun _ => (1 : ℝ)) i) ∧
    (∀ i : Fin 1, Integrable (fun x : Unit => ‖(fun _ _ => (1 : ℂ)) i x‖ ^ 2)
      (Measure.dirac ())) ∧
    (∀ i : Fin 1, ∫ x : Unit, ‖(fun _ _ => (1 : ℂ)) i x‖ ^ 2 ∂(Measure.dirac ()) ≤
      (1 : ℝ) * (fun _ => (1 : ℝ)) i ^ 2) ∧
    ((1 : ℝ) ^ 2 ≤ 1 * ∫ x : Unit, ‖∑ i : Fin 1, (fun _ _ => (1 : ℂ)) i x *
      (fun _ _ => (1 : ℂ)) i x‖ ^ 2 ∂(Measure.dirac ())) := by
  refine ⟨fun _ _ => by simp, fun _ => integrable_const _, fun _ => by simp, by simp⟩
end GroundTheory.Heights₂.Heights.EffectiveHS
