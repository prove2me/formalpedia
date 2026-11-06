-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:45:55.953707+00:00
-- url     : https://prove2.me/submissions/a2e2933a-46d1-463d-a697-be83a2442df2

import Mathlib.LinearAlgebra.Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Grade
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeEndomorphism_mk

section
namespace QEC.Coding.AlgebraicGeometry
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
private theorem primaryTorsionGradeEndomorphism_add (p : Ideal R)
    (f g : M →ₗ[R] M) (i : ℕ) :
    letI := primaryTorsionGradeModule (M := M) p i
    primaryTorsionGradeEndomorphism p (f + g) i =
      primaryTorsionGradeEndomorphism p f i +
        primaryTorsionGradeEndomorphism p g i := by
  letI := primaryTorsionGradeModule (M := M) p i
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      simp only [LinearMap.add_apply]
      rw [primaryTorsionGradeEndomorphism_mk,
        primaryTorsionGradeEndomorphism_mk,
        primaryTorsionGradeEndomorphism_mk]
      rfl
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution [IsNoetherianRing R]
    [Module.Finite R M] (p : Ideal R) [p.IsMaximal]
    (f g : M →ₗ[R] M) (n : ℕ) :
    primaryTorsionTrace p (f + g) n =
      primaryTorsionTrace p f n + primaryTorsionTrace p g n := by
  classical
  rw [primaryTorsionTrace, primaryTorsionTrace, primaryTorsionTrace,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI := primaryTorsionGradeModule (M := M) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p M i) :=
    primaryTorsionGradeFinite (M := M) p i
  rw [primaryTorsionGradeTrace, primaryTorsionGradeTrace,
    primaryTorsionGradeTrace, primaryTorsionGradeEndomorphism_add, map_add]
end QEC.Coding.AlgebraicGeometry
