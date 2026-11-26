-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexAt_conjLinear_apply_acd790c1e285
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:03:25.228862+00:00
-- url     : https://prove2.me/submissions/09b9bd74-edf9-4076-b580-95cde60c60da

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexAt
variable {K : Type*} {_ : Field K} (σ : K →+* ℂ)
theorem _root_.solution (z : ComplexAt σ) : conjLinear σ z = conj σ z := by
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
    | (intros; simp [ComplexAt, conj, conjLinear]; done)
    | (intros; grind)
    | (intros; grind [ComplexAt, conj, conjLinear])
    | (intros; unfold ComplexAt conj conjLinear; grind)
    | (intros; simp only [ComplexAt, conj, conjLinear] at * <;> grind)
    | (intros; simp_all [ComplexAt, conj, conjLinear] <;> grind)
    | (intros; ext <;> grind [ComplexAt, conj, conjLinear])
    | (intros; constructor <;> intro _ <;> grind [ComplexAt, conj, conjLinear])
    | (intro x; cases x <;> grind [ComplexAt, conj, conjLinear])
    | (intro x; induction x <;> simp_all [ComplexAt, conj, conjLinear])
    | (intro x y; induction x <;> grind [ComplexAt, conj, conjLinear])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [ComplexAt, conj, conjLinear])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [ComplexAt, conj, conjLinear])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_30_1"



end 
