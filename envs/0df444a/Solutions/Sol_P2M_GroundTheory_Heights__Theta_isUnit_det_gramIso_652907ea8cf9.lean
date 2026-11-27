-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_isUnit_det_gramIso_652907ea8cf9
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:16:02.640067+00:00
-- url     : https://prove2.me/submissions/a6fe2917-d7b4-48fc-9505-f4c1e1dce11a

import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Automorphic Matrix
theorem _root_.solution : IsUnit gramIso.det := by
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
    | (intros; simp [gramIso]; done)
    | (intros; grind)
    | (intros; grind [gramIso])
    | (intros; unfold gramIso; grind)
    | (intros; simp only [gramIso] at * <;> grind)
    | (intros; simp_all [gramIso] <;> grind)
    | (intros; ext <;> grind [gramIso])
    | (intros; constructor <;> intro _ <;> grind [gramIso])
    | (intro x; cases x <;> grind [gramIso])
    | (intro x; induction x <;> simp_all [gramIso])
    | (intro x y; induction x <;> grind [gramIso])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [gramIso])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [gramIso])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_5_1"



