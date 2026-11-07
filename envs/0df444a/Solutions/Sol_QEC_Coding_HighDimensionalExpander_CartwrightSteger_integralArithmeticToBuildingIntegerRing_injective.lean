-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToBuildingIntegerRing_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:00:42.891209+00:00
-- url     : https://prove2.me/submissions/98a599f1-ef1d-4fea-b82b-adf1886fcb08

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.RingTheory.PowerSeries.Inverse
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmetic_completion_compatibility_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmeticToFunctionField_injective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_functionFieldToBuildingLocalField_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) :
    Function.Injective (integralArithmeticToBuildingIntegerRing P) := by
  intro x y h
  apply integralArithmeticToFunctionField_injective P
  apply functionFieldToBuildingLocalField_injective P
  rw [← integralArithmetic_completion_compatibility_apply P x,
    ← integralArithmetic_completion_compatibility_apply P y, h]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
