-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicPatchAtPlace_mem_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:41:31.429897+00:00
-- url     : https://prove2.me/submissions/27cecd9b-e972-4a10-8ff5-1cd5310819ce

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_one_mem_arithmeticAdicCyclicIntegralLattice
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicSupportedAtPlace_mem_integral_iff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v)
    (hx : x ∈ ArithmeticAdicCyclicIntegralLattice P r v) :
    arithmeticFiniteAdeleCyclicPatchAtPlace P r v x ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r := by
  apply ArithmeticFiniteAdeleCyclicIntegralLattice.add_mem P r
  · apply ArithmeticFiniteAdeleCyclicIntegralLattice.sub_mem P r
    · exact one_mem_arithmeticFiniteAdeleCyclicIntegralLattice P r
    · exact
        (arithmeticFiniteAdeleCyclicSupportedAtPlace_mem_integral_iff
          P r v 1).mpr
            (one_mem_arithmeticAdicCyclicIntegralLattice P r v)
  · exact
      (arithmeticFiniteAdeleCyclicSupportedAtPlace_mem_integral_iff
        P r v x).mpr hx
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
