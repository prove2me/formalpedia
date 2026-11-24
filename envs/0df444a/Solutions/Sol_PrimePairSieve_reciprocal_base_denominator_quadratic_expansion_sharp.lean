-- Prove2me | solution 1 for PrimePairSieve.reciprocal_base_denominator_quadratic_expansion_sharp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T14:25:38.200993+00:00
-- url     : https://prove2.me/submissions/b30f446d-eea0-45e4-a516-341c3a4a4275
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_quadratic_expansion_sharp_transfer
import Theorems.Thm_PrimePairSieve_base_denominator_quadratic_expansion_sharp
open scoped BigOperators

theorem solution :
∃ B E : ℝ, 0 ≤ E ∧ E ≤ 10 / 3 ∧ (-(3 / 2) : ℝ) ≤ B ∧
      (∀ z : ℝ, 0 < z →
        |(∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree n then
            ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (n : ℝ) / z)) -
        (Real.log z ^ 2 +
          (4 * Real.eulerMascheroniConstant +
            4 * (∑' p : Nat.Primes,
              Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) - Real.log 2) *
            Real.log z + B) / (2 * TaoFivePrimes.twinPrimeConstant)| ≤
        E * z ^ (-(1 / 3 : ℝ))) := by
  exact PrimePairSieve.reciprocal_base_denominator_quadratic_expansion_sharp_transfer
    PrimePairSieve.base_denominator_quadratic_expansion_sharp
