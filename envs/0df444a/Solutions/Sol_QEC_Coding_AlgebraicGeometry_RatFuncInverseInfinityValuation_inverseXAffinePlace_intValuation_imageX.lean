-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.inverseXAffinePlace_intValuation_imageX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:08:03.966639+00:00
-- url     : https://prove2.me/submissions/cc7d36db-2f30-4bf7-9e42-a1ae3cbd3ef5

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalFieldPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncInverseInfinityValuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncInverseInfinityValuation_inverseXIdeal_eq_span_imageX
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncInverseInfinityValuation_inverseIntegralClosureEquiv_X_ne_zero

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
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    inverseXAffinePlace.intValuation (inverseIntegralClosureEquiv Polynomial.X) =
      WithZero.exp (-1 : Int) := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  exact inverseXAffinePlace.intValuation_singleton
    inverseIntegralClosureEquiv_X_ne_zero inverseXIdeal_eq_span_imageX
end QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation
