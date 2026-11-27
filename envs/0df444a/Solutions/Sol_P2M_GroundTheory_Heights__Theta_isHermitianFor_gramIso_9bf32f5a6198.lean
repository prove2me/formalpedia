-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_isHermitianFor_gramIso_9bf32f5a6198
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:16:00.71872+00:00
-- url     : https://prove2.me/submissions/84d6893d-92eb-4f59-8f9c-4551f1b50212

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
theorem _root_.solution : IsHermitianFor (conjHom ℚ GaussQ) gramIso := by
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
    | (intros; simp [IsHermitianFor, conjHom, GaussQ, gramIso]; done)
    | (intros; grind)
    | (intros; grind [IsHermitianFor, conjHom, GaussQ, gramIso])
    | (intros; unfold IsHermitianFor conjHom GaussQ gramIso; grind)
    | (intros; simp only [IsHermitianFor, conjHom, GaussQ, gramIso] at * <;> grind)
    | (intros; simp_all [IsHermitianFor, conjHom, GaussQ, gramIso] <;> grind)
    | (intros; ext <;> grind [IsHermitianFor, conjHom, GaussQ, gramIso])
    | (intros; constructor <;> intro _ <;> grind [IsHermitianFor, conjHom, GaussQ, gramIso])
    | (intro x; cases x <;> grind [IsHermitianFor, conjHom, GaussQ, gramIso])
    | (intro x; induction x <;> simp_all [IsHermitianFor, conjHom, GaussQ, gramIso])
    | (intro x y; induction x <;> grind [IsHermitianFor, conjHom, GaussQ, gramIso])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [IsHermitianFor, conjHom, GaussQ, gramIso])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [IsHermitianFor, conjHom, GaussQ, gramIso])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_4_2"



