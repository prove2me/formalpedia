-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:33:37.306713+00:00
-- url     : https://prove2.me/submissions/cbac3c3d-905a-48bc-abe7-1b90832a804c

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_arithmeticFiniteAdeleCyclicNonintegralPlaces_iff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    v ∈ arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r u ↔
      (arithmeticFiniteAdeleCyclicUnitAtPlace P r v u :
          ArithmeticAdicCyclicAlgebra P r v) ∉
          ArithmeticAdicCyclicIntegralLattice P r v ∨
        (((arithmeticFiniteAdeleCyclicUnitAtPlace P r v u)⁻¹ :
          (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
            ArithmeticAdicCyclicAlgebra P r v) ∉
          ArithmeticAdicCyclicIntegralLattice P r v := by
  rw [arithmeticFiniteAdeleCyclicUnitDenominatorPlaces, Set.mem_union,
    mem_arithmeticFiniteAdeleCyclicNonintegralPlaces_iff,
    mem_arithmeticFiniteAdeleCyclicNonintegralPlaces_iff]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
