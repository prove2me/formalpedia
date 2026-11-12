-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleAt_supportedAtPlace_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:24:18.083172+00:00
-- url     : https://prove2.me/submissions/2ace1399-5b98-41c9-9a13-ebbdbb6a5803

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime)
    (v w : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hvw : w ≠ v)
    (x : v.adicCompletion (FunctionField P)) :
    arithmeticFiniteAdeleAt P w
        (arithmeticFiniteAdeleSupportedAtPlace P v x) = 0 := by
  classical
  change Pi.single v x w = 0
  rw [Pi.single_eq_of_ne hvw]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
