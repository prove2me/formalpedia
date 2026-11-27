-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_isUnit_det_gramAniso_f8530161c17c
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:16:04.380306+00:00
-- url     : https://prove2.me/submissions/78facc3a-bbbe-48f1-8019-e081c85fa230

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
theorem _root_.solution : IsUnit gramAniso.det := by
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
    | (intros; simp [gramAniso]; done)
    | (intros; grind)
    | (intros; grind [gramAniso])
    | (intros; unfold gramAniso; grind)
    | (intros; simp only [gramAniso] at * <;> grind)
    | (intros; simp_all [gramAniso] <;> grind)
    | (intros; ext <;> grind [gramAniso])
    | (intros; constructor <;> intro _ <;> grind [gramAniso])
    | (intro x; cases x <;> grind [gramAniso])
    | (intro x; induction x <;> simp_all [gramAniso])
    | (intro x y; induction x <;> grind [gramAniso])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [gramAniso])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [gramAniso])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_5_2"



