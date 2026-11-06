-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:15:37.415891+00:00
-- url     : https://prove2.me/submissions/67a24af0-075e-4326-8567-4040052b57f6

import Mathlib.LinearAlgebra.Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Grade
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeEndomorphism_mk

section
namespace QEC.Coding.AlgebraicGeometry
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
private theorem primaryTorsionGradeEndomorphism_zero (p : Ideal R) (i : ℕ) :
    letI := primaryTorsionGradeModule (M := M) p i
    primaryTorsionGradeEndomorphism p (0 : M →ₗ[R] M) i = 0 := by
  letI := primaryTorsionGradeModule (M := M) p i
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      rw [primaryTorsionGradeEndomorphism_mk]
      rfl
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution [IsNoetherianRing R]
    [Module.Finite R M] (p : Ideal R) [p.IsMaximal] (n : ℕ) :
    primaryTorsionTrace p (0 : M →ₗ[R] M) n = 0 := by
  classical
  rw [primaryTorsionTrace]
  apply Finset.sum_eq_zero
  intro i hi
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI := primaryTorsionGradeModule (M := M) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p M i) :=
    primaryTorsionGradeFinite (M := M) p i
  rw [primaryTorsionGradeTrace, primaryTorsionGradeEndomorphism_zero,
    map_zero]
end QEC.Coding.AlgebraicGeometry
