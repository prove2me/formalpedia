-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_hyps_inhabited_46f781056f6e
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:08:06.808244+00:00
-- url     : https://prove2.me/submissions/0702a46e-c35f-454a-9acc-2cb263e07a4b

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
import Mathlib
import Mathlib.Tactic



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
theorem _root_.solution :
    (∀ (i : Fin 1) (x : Unit), ‖(fun _ _ => (1 : ℂ)) i x‖ ≤ (fun _ => (1 : ℝ)) i) ∧
    (∀ i : Fin 1, Integrable (fun x : Unit => ‖(fun _ _ => (1 : ℂ)) i x‖ ^ 2)
      (Measure.dirac ())) ∧
    (∀ i : Fin 1, ∫ x : Unit, ‖(fun _ _ => (1 : ℂ)) i x‖ ^ 2 ∂(Measure.dirac ()) ≤
      (1 : ℝ) * (fun _ => (1 : ℝ)) i ^ 2) ∧
    ((1 : ℝ) ^ 2 ≤ 1 * ∫ x : Unit, ‖∑ i : Fin 1, (fun _ _ => (1 : ℂ)) i x *
      (fun _ _ => (1 : ℂ)) i x‖ ^ 2 ∂(Measure.dirac ())) := by
  first
    | (intros; rfl)
    | (intros; ext; rfl)
    | (intros; exact LinearMap.ext fun _ => rfl)
    | (intros; apply Subtype.ext; rfl)
    | (intros; infer_instance)
    | (refine ⟨?_, ?_⟩ <;> infer_instance)
    | (intros; ext; simp; done)
    | (intros; assumption)
    | (intros; omega)
    | (intros; simp []; done)
    | (intros; grind)
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_0_3"



