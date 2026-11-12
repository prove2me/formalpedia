-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleSupportedAtPlace_mem_integral_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:24:31.317386+00:00
-- url     : https://prove2.me/submissions/5be8442b-9722-4f4e-99c8-3a704cfd9552

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : v.adicCompletion (FunctionField P)) :
    arithmeticFiniteAdeleSupportedAtPlace P v x ∈
        ArithmeticIntegralFiniteAdeles P ↔
      x ∈ v.adicCompletionIntegers (FunctionField P) := by
  classical
  constructor
  · intro hx
    have hv := hx v
    change Pi.single v x v ∈
      v.adicCompletionIntegers (FunctionField P) at hv
    rw [Pi.single_eq_same] at hv
    exact hv
  · intro hx w
    by_cases hwv : w = v
    · subst w
      change Pi.single v x v ∈
        v.adicCompletionIntegers (FunctionField P)
      rw [Pi.single_eq_same]
      exact hx
    · change Pi.single v x w ∈
          w.adicCompletionIntegers (FunctionField P)
      rw [Pi.single_eq_of_ne hwv]
      exact (w.adicCompletionIntegers (FunctionField P)).zero_mem
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
