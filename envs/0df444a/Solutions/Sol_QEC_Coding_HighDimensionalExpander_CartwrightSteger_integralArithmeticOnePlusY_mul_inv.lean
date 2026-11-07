-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralArithmeticOnePlusY_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:28:21.327636+00:00
-- url     : https://prove2.me/submissions/698ab8ec-37e5-42ba-8239-06ead600ff31

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.RingTheory.PowerSeries.Inverse
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_Arithmetic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) :
    (1 + integralArithmeticY P) *
        integralArithmeticOnePlusYInv P = 1 := by
  rw [integralArithmeticY, integralArithmeticOnePlusYInv]
  have hOne :
      1 + algebraMap (PolynomialRing P) (IntegralArithmeticRing P)
          Polynomial.X =
        algebraMap (PolynomialRing P) (IntegralArithmeticRing P)
          (1 + Polynomial.X) := by
    rw [map_add, map_one]
  rw [hOne]
  exact IsLocalization.Away.mul_invSelf
    (S := IntegralArithmeticRing P)
    (1 + Polynomial.X : PolynomialRing P)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
