-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionLayer_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:15:36.011832+00:00
-- url     : https://prove2.me/submissions/fbce15d9-58ff-4397-9035-197734da9cff

import Mathlib.Algebra.Module.Torsion.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Grade

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (p : Ideal R) (i j : ℕ) (hij : i ≤ j) :
    primaryTorsionLayer p M i ≤ primaryTorsionLayer p M j := by
  exact Submodule.torsionBySet_le_torsionBySet_pow i j hij p
end QEC.Coding.AlgebraicGeometry
