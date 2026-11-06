-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseChart.rationalMap_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:43:49.646213+00:00
-- url     : https://prove2.me/submissions/cd3d5200-134f-403d-91fe-94e06cd7c3e0

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
namespace QEC.Coding.AlgebraicGeometry.InverseChart
theorem _root_.solution :
    rationalMap k F RatFunc.X = inverseCoordinate k F := by
  simp [rationalMap, rationalEquiv]
end QEC.Coding.AlgebraicGeometry.InverseChart
