-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionGradeEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:16:16.701573+00:00
-- url     : https://prove2.me/submissions/fe83441f-8ad2-44d7-843f-9603755750e7

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceEquivScoped

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (p : Ideal R) (e : M ≃ₗ[R] N)
    (i : ℕ) (x : primaryTorsionLayer p M (i + 1)) :
    letI := primaryTorsionGradeModule (M := M) p i
    letI := primaryTorsionGradeModule (M := N) p i
    primaryTorsionGradeEquiv p e i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (primaryTorsionLayerEquiv p e (i + 1) x) :=
  rfl
end QEC.Coding.AlgebraicGeometry
