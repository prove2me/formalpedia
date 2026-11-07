-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToBuildingIntegerRing_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:39:36.659484+00:00
-- url     : https://prove2.me/submissions/2556bd76-af9e-45d2-bde3-d7134d7ac177

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.RingTheory.PowerSeries.Inverse
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (f : PolynomialRing P) :
    integralArithmeticToBuildingIntegerRing P
        (algebraMap (PolynomialRing P) (IntegralArithmeticRing P) f) =
      Polynomial.coeToPowerSeries.ringHom f := by
  exact IsLocalization.Away.lift_eq _ _ _
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
