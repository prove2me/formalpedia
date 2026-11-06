-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionGradeTrace_eq_of_intertwining
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:19:49.548609+00:00
-- url     : https://prove2.me/submissions/37498810-6b44-4847-8bd7-47ab0e178fda

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceEquivScoped
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeEndomorphism_mk

section
namespace QEC.Coding.AlgebraicGeometry
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
private theorem traceEquiv_primaryTorsionGradeEquiv_intertwines (p : Ideal R)
    (e : M ≃ₗ[R] N) (f : M →ₗ[R] M) (g : N →ₗ[R] N)
    (hfg : (e : M →ₗ[R] N).comp f = g.comp (e : M →ₗ[R] N))
    (i : ℕ) (q : primaryTorsionGrade p M i) :
    letI := primaryTorsionGradeModule (M := M) p i
    letI := primaryTorsionGradeModule (M := N) p i
    primaryTorsionGradeEquiv p e i
        (primaryTorsionGradeEndomorphism p f i q) =
      primaryTorsionGradeEndomorphism p g i
        (primaryTorsionGradeEquiv p e i q) := by
  letI := primaryTorsionGradeModule (M := M) p i
  letI := primaryTorsionGradeModule (M := N) p i
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      rw [primaryTorsionGradeEndomorphism_mk,
        primaryTorsionGradeEquiv_mk,
        primaryTorsionGradeEquiv_mk,
        primaryTorsionGradeEndomorphism_mk]
      congr 2
      apply Subtype.ext
      exact LinearMap.congr_fun hfg (x : M)
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution [IsNoetherianRing R]
    [Module.Finite R M] [Module.Finite R N] (p : Ideal R) [p.IsMaximal]
    (e : M ≃ₗ[R] N) (f : M →ₗ[R] M) (g : N →ₗ[R] N)
    (hfg : (e : M →ₗ[R] N).comp f = g.comp (e : M →ₗ[R] N))
    (i : ℕ) :
    primaryTorsionGradeTrace p f i = primaryTorsionGradeTrace p g i := by
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI := primaryTorsionGradeModule (M := M) p i
  letI := primaryTorsionGradeModule (M := N) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p M i) :=
    primaryTorsionGradeFinite (M := M) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p N i) :=
    primaryTorsionGradeFinite (M := N) p i
  let E := primaryTorsionGradeEquiv p e i
  let fgrade := primaryTorsionGradeEndomorphism p f i
  let ggrade := primaryTorsionGradeEndomorphism p g i
  have hconj : E.conj fgrade = ggrade := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := E.surjective y
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact traceEquiv_primaryTorsionGradeEquiv_intertwines p e f g hfg i x
  change LinearMap.trace (R ⧸ p) (primaryTorsionGrade p M i) fgrade =
    LinearMap.trace (R ⧸ p) (primaryTorsionGrade p N i) ggrade
  calc
    _ = LinearMap.trace (R ⧸ p) (primaryTorsionGrade p N i)
        (E.conj fgrade) := (LinearMap.trace_conj' fgrade E).symm
    _ = _ := congrArg (LinearMap.trace (R ⧸ p) _) hconj
end QEC.Coding.AlgebraicGeometry
