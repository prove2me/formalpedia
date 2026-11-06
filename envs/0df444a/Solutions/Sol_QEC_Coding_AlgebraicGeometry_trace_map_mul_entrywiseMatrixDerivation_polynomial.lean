-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.trace_map_mul_entrywiseMatrixDerivation_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:19:08.465505+00:00
-- url     : https://prove2.me/submissions/ab8e834e-67d7-4468-857a-4733f1d13ec4

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_map_polynomial

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
variable {k : Type*} [Field k]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {n : Type*} [Fintype n] [DecidableEq n]
    (Pinv P : Matrix n n k[X]) :
    Matrix.trace
        ((algebraMap k[X] (RatFunc k)).mapMatrix Pinv *
          entrywiseMatrixDerivation
            (RatFuncDerivation.rationalDerivation
              (k := k) (M := RatFunc k) 1)
            ((algebraMap k[X] (RatFunc k)).mapMatrix P)) =
      algebraMap k[X] (RatFunc k)
        (Matrix.trace (Pinv * entrywisePolynomialDerivative P)) := by
  rw [entrywiseMatrixDerivation_map_polynomial]
  rw [← (algebraMap k[X] (RatFunc k)).mapMatrix.map_mul]
  exact
    (AddMonoidHom.map_trace
      (algebraMap k[X] (RatFunc k)).toAddMonoidHom
      (Pinv * entrywisePolynomialDerivative P)).symm
end QEC.Coding.AlgebraicGeometry
