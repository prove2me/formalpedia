-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.ArithmeticPSLFamily.eventually_positiveProbability_good_arithmetic_family_of_complex_spectral_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:57:23.893505+00:00
-- url     : https://prove2.me/submissions/9b5e4450-2165-4252-983b-e3ff37939d8a

import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLFamily
import Definitions.Def_QEC_Coding_QuantumTanner_SpectralFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_PrimeFieldParameters
import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLGoodness
import Theorems.Thm_QEC_Coding_QuantumTanner_ArithmeticPSLFamily_exists_eventual_sample_of_spectral_bounds
import Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_iff_exists
import Theorems.Thm_QEC_Coding_SmallSetExpansion_HasMeanZeroComplexOperatorBound_toReal
import Theorems.Thm_QEC_Coding_SmallSetExpansion_HasMeanZeroOperatorBound_toBilinearBound


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.ArithmeticPSLFamily
open Classical QEC.Coding.ExpanderCodes.QuaternionGenerators QEC.Coding.SmallSetExpansion
variable (p : ℕ) [Fact p.Prime] (hOdd : 3 ≤ p)
  (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0)
namespace QEC.Coding.QuantumTanner.ArithmeticPSLFamily
theorem _root_.solution
    (delta eta rho : ℝ) (hDelta : 0 < delta) (hDeltaHalf : delta < 1 / 2)
    (hEta : 0 < eta) (hEtaHalf : eta < 1 / 2)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ t : ℕ, ∀ (p : ℕ) [Fact p.Prime] (hOdd : 3 ≤ p)
      (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0),
      (∀ r : ZMod p, r ^ 2 ≠ epsilon) → t ≤ p + 1 →
      (∀ n : ℕ,
        HasMeanZeroComplexOperatorBound
          (squareComplex p hOdd epsilon hEpsilon n).leftCayleyGraph
          (2 * Real.sqrt ((p + 1 : ℕ) : ℝ)) ∧
        HasMeanZeroComplexOperatorBound
          (squareComplex p hOdd epsilon hEpsilon n).rightCayleyGraph
          (2 * Real.sqrt ((p + 1 : ℕ) : ℝ))) →
      HasPositiveUniformProbability
        (HasGoodSampleFamily (left p hOdd epsilon hEpsilon) (right p hOdd epsilon hEpsilon)
          (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
          (left_injective p hOdd epsilon hEpsilon) (right_injective p hOdd epsilon hEpsilon)
          (left_inverse p hOdd epsilon hEpsilon) (right_inverse p hOdd epsilon hEpsilon)
          (total_nonconjugacy p hOdd epsilon hEpsilon) delta eta rho (p + 1)) := by
  obtain ⟨t, ht⟩ := exists_eventual_sample_of_spectral_bounds
    delta eta rho hDelta hDeltaHalf hEta hEtaHalf hRho hRhoHalf hEntropy
  refine ⟨t, ?_⟩
  intro p _ hOdd epsilon hEpsilon hNonSquare hLarge hRamanujan
  obtain ⟨sample, hSample⟩ := ht p hOdd epsilon hEpsilon hNonSquare hLarge
  apply (hasPositiveUniformProbability_iff_exists _).mpr
  refine ⟨sample, hSample ?_ ?_⟩
  · intro n
    exact HasMeanZeroOperatorBound.toBilinearBound (by positivity)
      (hRamanujan n).1.toReal
  · intro n
    exact HasMeanZeroOperatorBound.toBilinearBound (by positivity)
      (hRamanujan n).2.toReal
end QEC.Coding.QuantumTanner.ArithmeticPSLFamily
