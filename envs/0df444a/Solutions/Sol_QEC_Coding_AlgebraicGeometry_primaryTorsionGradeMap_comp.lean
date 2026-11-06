-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionGradeMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:15:45.08167+00:00
-- url     : https://prove2.me/submissions/1c108bff-d870-4212-936b-44d6ec0df8e4

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceFunctorial
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeMap_mk

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {P : Type*} [AddCommGroup P] [Module R P]
    (p : Ideal R) (g : N →ₗ[R] P) (f : M →ₗ[R] N) (i : ℕ) :
    letI := primaryTorsionGradeModule (M := M) p i
    letI := primaryTorsionGradeModule (M := N) p i
    letI := primaryTorsionGradeModule (M := P) p i
    primaryTorsionGradeMap p (g.comp f) i =
      (primaryTorsionGradeMap p g i).comp
        (primaryTorsionGradeMap p f i) := by
  letI := primaryTorsionGradeModule (M := M) p i
  letI := primaryTorsionGradeModule (M := N) p i
  letI := primaryTorsionGradeModule (M := P) p i
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      rw [primaryTorsionGradeMap_mk]
      simp only [LinearMap.comp_apply]
      rw [primaryTorsionGradeMap_mk, primaryTorsionGradeMap_mk]
      rfl
end QEC.Coding.AlgebraicGeometry
