-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.inverseXFibreGlobalPlace_eq_rationalInfinity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:19:22.694771+00:00
-- url     : https://prove2.me/submissions/ac3469d0-9a30-4623-aee9-3215bf2f3089

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalFieldPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncInverseInfinityValuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncInverseInfinityValuation_inverseXFibreValuation_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_trivialOnConstants
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero


section
namespace QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation
open scoped Polynomial RatFunc WithZero
open RatFuncFixturePlaces
attribute [local instance] ratFuncDecidableEq
private theorem valuation_eq_infty_of_X_eq_exp_one
    (v : Valuation F ℤᵐ⁰) [v.IsTrivialOn K]
    (hx : v RatFunc.X = WithZero.exp (1 : Int)) :
    v = RatFunc.inftyValuation K := by
  classical
  ext f
  induction f using RatFunc.induction_on with
  | f p q hq =>
      rw [map_div₀, map_div₀]
      by_cases hp : p = 0
      · simp [hp]
      have hlt : 1 < v RatFunc.X := by
        rw [hx, ← WithZero.exp_zero]
        exact WithZero.exp_lt_exp.mpr (by norm_num)
      have hltInfinity : 1 < RatFunc.inftyValuation K RatFunc.X := by
        rw [RatFunc.inftyValuation.X, ← WithZero.exp_zero]
        exact WithZero.exp_lt_exp.mpr (by norm_num)
      change v (p : F) / v (q : F) =
        RatFunc.inftyValuation K (p : F) / RatFunc.inftyValuation K (q : F)
      rw [Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
          K (v := v) hlt hp,
        Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
          K (v := v) hlt hq,
        Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
          K (v := RatFunc.inftyValuation K) hltInfinity hp,
        Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
          K (v := RatFunc.inftyValuation K) hltInfinity hq]
      simp [hx, RatFunc.inftyValuation.X]
private theorem globalPlace_eq_of_valuation_eq
    {P Q : GlobalPlace K F} (hvaluation : P.valuation = Q.valuation) : P = Q := by
  cases P
  cases Q
  cases hvaluation
  rfl
end QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation
end

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
    inverseXFibreGlobalPlace = GlobalPlace.rationalInfinity K := by
  apply globalPlace_eq_of_valuation_eq
  letI : inverseXFibreValuation.IsTrivialOn K :=
    GlobalPlace.trivialOnConstants inverseXFibreGlobalPlace
  exact valuation_eq_infty_of_X_eq_exp_one inverseXFibreValuation inverseXFibreValuation_X
end QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation
