-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.transportedPolynomialMap_X_eq_original_X_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:07:19.33997+00:00
-- url     : https://prove2.me/submissions/dbeec3fc-4e76-4c33-8d9a-ab6ebd3d2424

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalFieldPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncInverseInfinityValuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_transportedRationalMap_X
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation
open scoped Polynomial RatFunc WithZero
open RatFuncFixturePlaces
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation._p2m_local_instance_de9b108ef9_13
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.oldRationalAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.oldPolynomialAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.oldScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.oldFunctionField
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.oldSeparable
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.oldFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.ratFuncDecidableEq
attribute [local instance] ratFuncDecidableEq
namespace QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation
theorem _root_.solution :
    InverseAffinePlace.transportedPolynomialMap (oldRationalAlgebra := oldRationalAlgebra) K F Polynomial.X =
      (RatFunc.X : F)⁻¹ := by
  simp [InverseAffinePlace.transportedPolynomialMap,
    InverseAffinePlace.transportedRationalMap_X, InverseChart.inverseCoordinate,
    InverseChart.coordinate]
end QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation
