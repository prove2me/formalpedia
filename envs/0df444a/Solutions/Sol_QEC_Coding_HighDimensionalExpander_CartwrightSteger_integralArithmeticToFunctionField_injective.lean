-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToFunctionField_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:28:19.280605+00:00
-- url     : https://prove2.me/submissions/d58c9255-9490-41d0-8424-ded1dc531958

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
    Function.Injective (integralArithmeticToFunctionField P) := by
  rw [IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (1 + Polynomial.X : PolynomialRing P))
    (integralArithmeticToFunctionField P)]
  intro f g
  simp only [integralArithmeticToFunctionField_algebraMap]
  constructor
  · intro h
    simpa only [integralArithmeticToFunctionField_algebraMap] using
      congrArg (integralArithmeticToFunctionField P) h
  · intro h
    have hfg : f = g := RatFunc.algebraMap_injective (BaseField P) h
    subst g
    rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
