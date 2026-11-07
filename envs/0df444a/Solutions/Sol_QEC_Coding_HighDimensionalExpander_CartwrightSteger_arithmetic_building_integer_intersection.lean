-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmetic_building_integer_intersection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:01:18.395428+00:00
-- url     : https://prove2.me/submissions/933e8683-6d36-4fea-bfc0-0515727c3785

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticIntersection
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_integralArithmetic_image_iff_denom_dvd
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_arithmetic_image_iff_denom_dvd
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_not_X_dvd_denom_of_building_integral
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToBuildingIntegerRing_algebraMap
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToBuildingIntegerRing_y
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToFunctionField_y
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToBuildingIntegerRing_algebraMap
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToBuildingIntegerRing_y
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToFunctionField_y
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (x : FunctionField P)
    (harithmetic : ∃ a : ArithmeticRing P,
      arithmeticRingToFunctionField P a = x)
    (hlocal : ∃ f : BuildingIntegerRing P,
      SphericalHecke.integerEmbedding (BaseField P) f =
        functionFieldToBuildingLocalField P x) :
    ∃ a : IntegralArithmeticRing P,
      integralArithmeticToFunctionField P a = x := by
  obtain ⟨n, hden⟩ :=
    (mem_arithmetic_image_iff_denom_dvd P x).mp harithmetic
  have hnot := not_X_dvd_denom_of_building_integral P x hlocal
  have hcop : IsCoprime x.denom (Polynomial.X ^ n) :=
    ((Polynomial.prime_X.coprime_iff_not_dvd.mpr hnot).symm).pow_right
  have hproduct : x.denom ∣
      Polynomial.X ^ n *
        (1 + Polynomial.X : PolynomialRing P) ^ n := by
    simpa only [mul_pow] using hden
  have htarget : x.denom ∣
      (1 + Polynomial.X : PolynomialRing P) ^ n :=
    hcop.dvd_of_dvd_mul_left hproduct
  exact (mem_integralArithmetic_image_iff_denom_dvd P x).mpr
    ⟨n, htarget⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
