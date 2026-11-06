-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseChart.polynomialMap_X
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:04:03.487303+00:00
-- url     : https://prove2.me/submissions/0e74746c-80ed-4215-8607-4e0aa26306b7

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.NumberTheory.FunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseChart
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.InverseChart
open scoped IntermediateField Polynomial RatFunc
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k k⟮X⟯ F]
variable [_root_.FunctionField k F]

theorem solution :
    polynomialMap k F Polynomial.X = inverseCoordinate k F := by
  simp [polynomialMap, rationalMap, rationalEquiv]
