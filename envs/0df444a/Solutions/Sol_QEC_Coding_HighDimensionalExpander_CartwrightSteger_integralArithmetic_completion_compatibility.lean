-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmetic_completion_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:28:18.10997+00:00
-- url     : https://prove2.me/submissions/29bc615f-7f48-464f-b111-c7786f026370

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.RingTheory.PowerSeries.Inverse
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToBuildingIntegerRing_algebraMap
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply


attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToBuildingIntegerRing_algebraMap

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) :
    (SphericalHecke.integerEmbedding (BaseField P)).comp
        (integralArithmeticToBuildingIntegerRing P) =
      (functionFieldToBuildingLocalField P).comp
        (integralArithmeticToFunctionField P) := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (1 + Polynomial.X : PolynomialRing P))
  apply RingHom.ext
  intro f
  simp only [RingHom.comp_apply,
    integralArithmeticToBuildingIntegerRing_algebraMap,
    integralArithmeticToFunctionField_algebraMap]
  exact RatFunc.coe_coe f
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
