-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionGradeTrace_comp_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:16:33.621202+00:00
-- url     : https://prove2.me/submissions/b2a4c686-b8ae-40cf-bb41-89fd26773062

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceFunctorial
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeMap_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeMap_comp
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeEndomorphism_mk

section
namespace QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
private theorem primaryTorsionGradeMap_self_eq_endomorphism
    (p : Ideal R) (f : M →ₗ[R] M) (i : ℕ) :
    letI := primaryTorsionGradeModule (M := M) p i
    primaryTorsionGradeMap p f i =
      primaryTorsionGradeEndomorphism p f i := by
  letI := primaryTorsionGradeModule (M := M) p i
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      rw [primaryTorsionGradeMap_mk,
        primaryTorsionGradeEndomorphism_mk]
      rfl
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution [IsNoetherianRing R]
    [Module.Finite R M] [Module.Finite R N]
    (p : Ideal R) [p.IsMaximal]
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) (i : ℕ) :
    primaryTorsionGradeTrace p (g.comp f) i =
      primaryTorsionGradeTrace p (f.comp g) i := by
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI := primaryTorsionGradeModule (M := M) p i
  letI := primaryTorsionGradeModule (M := N) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p M i) :=
    primaryTorsionGradeFinite (M := M) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p N i) :=
    primaryTorsionGradeFinite (M := N) p i
  change LinearMap.trace (R ⧸ p) (primaryTorsionGrade p M i)
      (primaryTorsionGradeEndomorphism p (g.comp f) i) =
    LinearMap.trace (R ⧸ p) (primaryTorsionGrade p N i)
      (primaryTorsionGradeEndomorphism p (f.comp g) i)
  rw [← primaryTorsionGradeMap_self_eq_endomorphism,
    ← primaryTorsionGradeMap_self_eq_endomorphism,
    primaryTorsionGradeMap_comp, primaryTorsionGradeMap_comp]
  exact LinearMap.trace_comp_comm'
    (primaryTorsionGradeMap p f i) (primaryTorsionGradeMap p g i)
end QEC.Coding.AlgebraicGeometry
