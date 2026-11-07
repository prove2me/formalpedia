-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmetic_completion_compatibility_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:29:19.904751+00:00
-- url     : https://prove2.me/submissions/946f8e9f-1134-42d2-99c7-8af848b05075

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.RingTheory.PowerSeries.Inverse
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_integralArithmetic_completion_compatibility

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (x : IntegralArithmeticRing P) :
    SphericalHecke.integerEmbedding (BaseField P)
        (integralArithmeticToBuildingIntegerRing P x) =
      functionFieldToBuildingLocalField P
        (integralArithmeticToFunctionField P x) := by
  exact RingHom.congr_fun (integralArithmetic_completion_compatibility P) x
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
