-- Prove2me | solution 2 for QEC.Coding.AlgebraicGeometry.InverseChart.polynomialMap_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:10.947751+00:00
-- url     : https://prove2.me/submissions/c493076b-d9ee-4c84-94c3-a56c2fb4c8cf

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.NumberTheory.FunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseChart
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseChart_rationalMap_X

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.InverseChart
open scoped IntermediateField Polynomial RatFunc
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k k⟮X⟯ F]
variable [_root_.FunctionField k F]
namespace QEC.Coding.AlgebraicGeometry.InverseChart
theorem _root_.solution :
    polynomialMap k F Polynomial.X = inverseCoordinate k F := by
  simpa [polynomialMap] using rationalMap_X k F
end QEC.Coding.AlgebraicGeometry.InverseChart
