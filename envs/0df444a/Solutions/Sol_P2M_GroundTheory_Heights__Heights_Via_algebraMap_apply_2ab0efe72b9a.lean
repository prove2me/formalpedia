-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Via_algebraMap_apply_2ab0efe72b9a
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:24:12.781934+00:00
-- url     : https://prove2.me/submissions/42d6ce8f-d9bf-4457-907d-fad2f31fd105

import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FinrankFibreAtOfIsInvertibleSheaf
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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
open GroundTheory.Heights₂.Heights.Via
variable {R : Type*} [CommRing R] (φ : R →+* ℂ)
theorem _root_.solution (r : R) : algebraMap R (Via φ) r = ofComplex φ (φ r) := by
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
    | (intros; simp [Via, ofComplex]; done)
    | (intros; grind)
    | (intros; grind [Via, ofComplex])
    | (intros; unfold Via ofComplex; grind)
    | (intros; simp only [Via, ofComplex] at * <;> grind)
    | (intros; simp_all [Via, ofComplex] <;> grind)
    | (intros; ext <;> grind [Via, ofComplex])
    | (intros; constructor <;> intro _ <;> grind [Via, ofComplex])
    | (intro x; cases x <;> grind [Via, ofComplex])
    | (intro x; induction x <;> simp_all [Via, ofComplex])
    | (intro x y; induction x <;> grind [Via, ofComplex])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [Via, ofComplex])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [Via, ofComplex])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_27_1"



end 
