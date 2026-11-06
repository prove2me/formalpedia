-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionGradeEndomorphism_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:28:46.718245+00:00
-- url     : https://prove2.me/submissions/2d79645a-c880-4d7e-8210-ff3098195f87

import Mathlib.Algebra.Module.Torsion.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Grade

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (p : Ideal R)
    (f : M →ₗ[R] M) (i : ℕ) (x : primaryTorsionLayer p M (i + 1)) :
    letI := primaryTorsionGradeModule (M := M) p i
    primaryTorsionGradeEndomorphism p f i
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (primaryTorsionLayerEndomorphism p f (i + 1) x) :=
  rfl
end QEC.Coding.AlgebraicGeometry
