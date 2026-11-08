-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.ArithmeticPSLFamily.positiveProbability_good_arithmetic_family_of_complex_spectral_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:43:10.111918+00:00
-- url     : https://prove2.me/submissions/820cf875-1ddb-4f65-9097-9134b3b35408

import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLFamily
import Definitions.Def_QEC_Coding_QuantumTanner_SpectralFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_PrimeFieldParameters
import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLGoodness
import Theorems.Thm_QEC_Coding_QuantumTanner_ArithmeticPSLFamily_exists_good_arithmetic_family_of_complex_spectral_bounds
import Theorems.Thm_QEC_Coding_QuantumTanner_hasPositiveUniformProbability_iff_exists


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
    (hEntropy : Real.binEntropy delta < rho * Real.log 2)
    (hRamanujan : ∀ (p : ℕ) [Fact p.Prime] (hOdd : 3 ≤ p)
      (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0),
      (∀ r : ZMod p, r ^ 2 ≠ epsilon) → ∀ n : ℕ,
      HasMeanZeroComplexOperatorBound
        (squareComplex p hOdd epsilon hEpsilon n).leftCayleyGraph
        (2 * Real.sqrt ((p + 1 : ℕ) : ℝ)) ∧
      HasMeanZeroComplexOperatorBound
        (squareComplex p hOdd epsilon hEpsilon n).rightCayleyGraph
        (2 * Real.sqrt ((p + 1 : ℕ) : ℝ))) (N : ℕ) :
    ∃ (p : ℕ) (hPrime : p.Prime),
      letI : Fact p.Prime := ⟨hPrime⟩
      ∃ (hOdd : 3 ≤ p) (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0),
        N ≤ p + 1 ∧ (∀ r : ZMod p, r ^ 2 ≠ epsilon) ∧
        HasPositiveUniformProbability
          (HasGoodSampleFamily (left p hOdd epsilon hEpsilon) (right p hOdd epsilon hEpsilon)
            (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
            (left_injective p hOdd epsilon hEpsilon) (right_injective p hOdd epsilon hEpsilon)
            (left_inverse p hOdd epsilon hEpsilon) (right_inverse p hOdd epsilon hEpsilon)
            (total_nonconjugacy p hOdd epsilon hEpsilon) delta eta rho (p + 1)) := by
  obtain ⟨p, hPrime, hOdd, epsilon, hEpsilon, hLarge, hNonSquare, sample, hGood⟩ :=
    exists_good_arithmetic_family_of_complex_spectral_bounds
      delta eta rho hDelta hDeltaHalf hEta hEtaHalf hRho hRhoHalf hEntropy hRamanujan N
  letI : Fact p.Prime := ⟨hPrime⟩
  refine ⟨p, hPrime, hOdd, epsilon, hEpsilon, hLarge, hNonSquare, ?_⟩
  exact (hasPositiveUniformProbability_iff_exists _).mpr ⟨sample, hGood⟩
end QEC.Coding.QuantumTanner.ArithmeticPSLFamily
