-- Prove2me | solution 1 for P2M_GlobalTheory_algebra_OfHom_algebraMap_6568cc1e9975
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:20:02.160597+00:00
-- url     : https://prove2.me/submissions/86226cfc-5600-4c80-82a7-c72978b11b7d

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
theorem _root_.solution {R : Type u} [CommRing R] (f : X ⟶ Spec (.of R)) (r : R) :
    letI := algebraΓOfHom f
    algebraMap R Γ(X, ⊤) r = f.appTop ((Scheme.ΓSpecIso (.of R)).inv r) := by
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
    | (intros; simp [algebraΓOfHom]; done)
    | (intros; grind)
    | (intros; grind [algebraΓOfHom])
    | (intros; unfold algebraΓOfHom; grind)
    | (intros; simp only [algebraΓOfHom] at * <;> grind)
    | (intros; simp_all [algebraΓOfHom] <;> grind)
    | (intros; ext <;> grind [algebraΓOfHom])
    | (intros; constructor <;> intro _ <;> grind [algebraΓOfHom])
    | (intro x; cases x <;> grind [algebraΓOfHom])
    | (intro x; induction x <;> simp_all [algebraΓOfHom])
    | (intro x y; induction x <;> grind [algebraΓOfHom])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [algebraΓOfHom])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [algebraΓOfHom])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_18_1"



end 
