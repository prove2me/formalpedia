-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:41:32.999896+00:00
-- url     : https://prove2.me/submissions/4cd599bc-0bb6-4532-aa87-d6b3dedd212d

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
variable {k : Type*} [Field k]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution {m n : Type*}
    (A : Matrix m n k[X]) (i : m) (j : n) :
    entrywisePolynomialDerivative A i j = (A i j).derivative :=
  rfl
end QEC.Coding.AlgebraicGeometry
