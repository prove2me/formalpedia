-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitSupportedAtPlace_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:23:09.429204+00:00
-- url     : https://prove2.me/submissions/98d41fb0-8879-497b-9ff0-f2aaae3d451e

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
    Units.map
        (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v).toRingHom.toMonoidHom
        (arithmeticFiniteAdeleCyclicUnitSupportedAtPlace P r v u) = u := by
  apply Units.ext
  exact arithmeticFiniteAdeleCyclicAlgebraAtPlace_patch P r v u
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
