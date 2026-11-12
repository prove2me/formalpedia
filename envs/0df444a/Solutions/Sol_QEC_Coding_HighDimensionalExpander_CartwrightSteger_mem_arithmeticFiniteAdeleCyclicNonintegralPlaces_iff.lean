-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_arithmeticFiniteAdeleCyclicNonintegralPlaces_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:28:31.79564+00:00
-- url     : https://prove2.me/submissions/0dc425e1-cf21-43e8-9049-0d78be392cdd

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticAdicCyclicBasis_equivFun_atPlace

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    v ∈ arithmeticFiniteAdeleCyclicNonintegralPlaces P r x ↔
      arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v x ∉
        ArithmeticAdicCyclicIntegralLattice P r v := by
  constructor
  · rintro ⟨p, hp⟩ hlocal
    apply hp
    change arithmeticFiniteAdeleAt P v
      ((arithmeticFiniteAdeleCyclicBasis P r).equivFun x p) ∈
        v.adicCompletionIntegers (FunctionField P)
    rw [← arithmeticAdicCyclicBasis_equivFun_atPlace P r v x p]
    exact hlocal p
  · intro hlocal
    change ¬ ∀ p, (arithmeticAdicCyclicBasis P r v).equivFun
      (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v x) p ∈
        v.adicCompletionIntegers (FunctionField P) at hlocal
    push Not at hlocal
    obtain ⟨p, hp⟩ := hlocal
    refine ⟨p, ?_⟩
    change arithmeticFiniteAdeleAt P v
      ((arithmeticFiniteAdeleCyclicBasis P r).equivFun x p) ∉
        v.adicCompletionIntegers (FunctionField P)
    rw [← arithmeticAdicCyclicBasis_equivFun_atPlace P r v x p]
    exact hp
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
