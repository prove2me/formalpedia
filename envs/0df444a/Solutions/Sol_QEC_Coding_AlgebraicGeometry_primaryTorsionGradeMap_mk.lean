-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionGradeMap_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:45:56.86083+00:00
-- url     : https://prove2.me/submissions/70997f7a-cbb5-4b32-8781-989350b87557

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceFunctorial

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (p : Ideal R) (f : M →ₗ[R] N)
    (i : ℕ) (x : primaryTorsionLayer p M (i + 1)) :
    letI := primaryTorsionGradeModule (M := M) p i
    letI := primaryTorsionGradeModule (M := N) p i
    primaryTorsionGradeMap p f i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (primaryTorsionLayerMap p f (i + 1) x) :=
  rfl
end QEC.Coding.AlgebraicGeometry
