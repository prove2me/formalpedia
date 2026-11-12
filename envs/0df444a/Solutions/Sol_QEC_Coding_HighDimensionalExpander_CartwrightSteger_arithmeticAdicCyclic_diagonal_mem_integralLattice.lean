-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticAdicCyclic_diagonal_mem_integralLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:29:05.668046+00:00
-- url     : https://prove2.me/submissions/27611f75-42e2-46ff-8389-a3ddbae1b2a6

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticAdicCyclicBasis_equivFun_diagonal

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : CyclicAlgebra P r) (hx : x ∈ arithmeticCyclicSpan P r) :
    TensorProduct.tmul (FunctionField P) 1 x ∈
      ArithmeticAdicCyclicIntegralLattice P r v := by
  intro p
  obtain ⟨a, ha⟩ :=
    exists_arithmetic_coordinate_of_mem_arithmeticCyclicSpan P r x hx p
  rw [arithmeticAdicCyclicBasis_equivFun_diagonal, ← ha]
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem
    (ArithmeticRing P) (FunctionField P) v a
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
