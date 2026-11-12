-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.one_mem_arithmeticAdicCyclicIntegralLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:32:29.782046+00:00
-- url     : https://prove2.me/submissions/1cef9707-c7b6-4245-a105-42be6b6309ef

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticAdicCyclic_diagonal_mem_integralLattice
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_one_mem_arithmeticCyclicSpan


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    (1 : ArithmeticAdicCyclicAlgebra P r v) ∈
      ArithmeticAdicCyclicIntegralLattice P r v := by
  exact arithmeticAdicCyclic_diagonal_mem_integralLattice
    P r v 1 (one_mem_arithmeticCyclicSpan P r)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
