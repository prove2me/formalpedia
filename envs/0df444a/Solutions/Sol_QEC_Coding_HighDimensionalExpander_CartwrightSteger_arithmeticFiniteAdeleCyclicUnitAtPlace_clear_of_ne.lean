-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitAtPlace_clear_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:41:07.124299+00:00
-- url     : https://prove2.me/submissions/8f4d3f78-1bc6-4b99-8671-4978e3f03732

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicUnitSupportedAtPlace_projection_of_ne

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (v w : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hwv : w ≠ v)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    arithmeticFiniteAdeleCyclicUnitAtPlace P r w
        (arithmeticFiniteAdeleCyclicUnitClearAtPlace P r v u) =
      arithmeticFiniteAdeleCyclicUnitAtPlace P r w u := by
  rw [arithmeticFiniteAdeleCyclicUnitClearAtPlace, map_mul]
  change
    Units.map
        (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r w).toRingHom.toMonoidHom
        (arithmeticFiniteAdeleCyclicUnitSupportedAtPlace P r v
          ((arithmeticFiniteAdeleCyclicUnitAtPlace P r v u)⁻¹)) *
      arithmeticFiniteAdeleCyclicUnitAtPlace P r w u = _
  rw [arithmeticFiniteAdeleCyclicUnitSupportedAtPlace_projection_of_ne
    P r v w hwv, one_mul]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
