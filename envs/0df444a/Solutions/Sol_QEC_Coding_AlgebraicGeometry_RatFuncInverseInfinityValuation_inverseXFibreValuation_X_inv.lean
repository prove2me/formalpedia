-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.inverseXFibreValuation_X_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:08:41.454035+00:00
-- url     : https://prove2.me/submissions/44a6e29b-be1f-4dc2-9bf7-61e283e67c9c

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalFieldPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncInverseInfinityValuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncInverseInfinityValuation_inverseXAffinePlace_intValuation_imageX
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncInverseInfinityValuation_transportedPolynomialMap_X_eq_original_X_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_globalPlace_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_valuation_of_integral
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_globalPlace_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncFixturePlaces_algebraMap_inverseIntegralClosureEquiv


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
    inverseXFibreValuation ((RatFunc.X : F)⁻¹) = WithZero.exp (-1 : Int) := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  have hintegral : inverseXFibreValuation
      (inverseIntegralClosureEquiv Polynomial.X).1 = WithZero.exp (-1 : Int) := by
    unfold inverseXFibreValuation
    rw [InverseAffinePlace.globalPlace_valuation
      (oldPolynomialAlgebra := RatFuncFixturePlaces.oldPolynomialAlgebra)
      (oldRationalAlgebra := RatFuncFixturePlaces.oldRationalAlgebra)
      (oldScalarTower := RatFuncFixturePlaces.oldScalarTower)
      (oldFunctionField := RatFuncFixturePlaces.oldFunctionField)
      (oldSeparable := RatFuncFixturePlaces.oldSeparable)
      K F inverseXFibrePoint,
      AffinePlace.valuation_of_integral]
    change inverseXAffinePlace.intValuation (inverseIntegralClosureEquiv Polynomial.X) = _
    exact inverseXAffinePlace_intValuation_imageX
  have hmap : (inverseIntegralClosureEquiv Polynomial.X).1 =
      InverseAffinePlace.transportedPolynomialMap
        (oldRationalAlgebra := oldRationalAlgebra) K F Polynomial.X := by
    exact algebraMap_inverseIntegralClosureEquiv Polynomial.X
  rw [hmap,
    transportedPolynomialMap_X_eq_original_X_inv] at hintegral
  exact hintegral
end QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation
