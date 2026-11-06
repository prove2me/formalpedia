-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.inverseXFibreValuation_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:09:29.083758+00:00
-- url     : https://prove2.me/submissions/4ad8ea27-1812-45ed-8b9e-635133ee8a81

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalFieldPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncInverseInfinityValuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncInverseInfinityValuation_inverseXFibreValuation_X_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
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
    inverseXFibreValuation RatFunc.X = WithZero.exp (1 : Int) := by
  calc
    inverseXFibreValuation RatFunc.X =
        (inverseXFibreValuation ((RatFunc.X : F)⁻¹))⁻¹ := by
          rw [(inverseXFibreValuation).map_inv, inv_inv]
    _ = (WithZero.exp (-1 : Int))⁻¹ := by rw [inverseXFibreValuation_X_inv]
    _ = WithZero.exp (1 : Int) := by simp
end QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation
