-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclicUnitSupportedAtPlace_denominatorPlaces_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:57:59.59117+00:00
-- url     : https://prove2.me/submissions/cafb18e3-d669-40e4-b79b-bea096751222

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclicPatchAtPlace_mem_integral
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleCyclic_mem_integralLattice_iff_denominatorPlaces_empty


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticAdicCyclicAlgebra P r v)ˣ)
    (hu : (u : ArithmeticAdicCyclicAlgebra P r v) ∈
      ArithmeticAdicCyclicIntegralLattice P r v)
    (huInv : ((u⁻¹ : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
        ArithmeticAdicCyclicAlgebra P r v) ∈
      ArithmeticAdicCyclicIntegralLattice P r v) :
    arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r
        (arithmeticFiniteAdeleCyclicUnitSupportedAtPlace P r v u) = ∅ := by
  have hval :=
    (arithmeticFiniteAdeleCyclic_mem_integralLattice_iff_denominatorPlaces_empty
      P r _).mp
      (arithmeticFiniteAdeleCyclicPatchAtPlace_mem_integral P r v u hu)
  have hinv :=
    (arithmeticFiniteAdeleCyclic_mem_integralLattice_iff_denominatorPlaces_empty
      P r _).mp
      (arithmeticFiniteAdeleCyclicPatchAtPlace_mem_integral P r v
        ((u⁻¹ : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
          ArithmeticAdicCyclicAlgebra P r v) huInv)
  rw [arithmeticFiniteAdeleCyclicUnitDenominatorPlaces]
  change arithmeticFiniteAdeleCyclicNonintegralPlaces P r
      (arithmeticFiniteAdeleCyclicPatchAtPlace P r v u) ∪
    arithmeticFiniteAdeleCyclicNonintegralPlaces P r
      (arithmeticFiniteAdeleCyclicPatchAtPlace P r v
        ((u⁻¹ : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
          ArithmeticAdicCyclicAlgebra P r v)) = ∅
  rw [hval, hinv, Set.empty_union]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
