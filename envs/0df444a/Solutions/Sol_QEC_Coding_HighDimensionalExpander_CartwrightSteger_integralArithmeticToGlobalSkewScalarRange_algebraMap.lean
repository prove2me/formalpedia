-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticToGlobalSkewScalarRange_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:57:48.146818+00:00
-- url     : https://prove2.me/submissions/b44490da-9ff5-447f-87cf-ceb13e623b0e

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCoordinates

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (f : PolynomialRing P) :
    integralArithmeticToGlobalSkewScalarRange P r
        (algebraMap (PolynomialRing P) (IntegralArithmeticRing P) f) =
      polynomialToGlobalSkewScalarRange P r f := by
  exact IsLocalization.Away.lift_eq _ _ _
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
