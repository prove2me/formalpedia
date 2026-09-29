-- Prove2me | solution 2 for OddPerfectNumber.no_dris_five_s_odd_ge_five
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-11T09:05:53.18898+00:00
-- url     : https://prove2.me/submissions/0e04591b-5784-4e10-a845-a205020ef79e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_dris_index_odd_prime_of_one_odd_prime
import Theorems.Thm_OddPerfectNumber_no_dris_index_odd_composite_of_one_odd_prime

/-!
Reduction of `OddPerfectNumber.no_dris_five_s_odd_ge_five`.

Since `k + 1 = 6` has the single odd prime divisor `3`, a prime index is excluded by
`OddPerfectNumber.no_dris_index_odd_prime_of_one_odd_prime`; the remaining case is an odd
composite index, which is the child lemma
`OddPerfectNumber.no_dris_index_odd_composite_of_one_odd_prime`.
-/

open Finset

theorem solution (p m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hs_not_even : ¬ Even s)
    (hs5 : 5 ≤ s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) := by
  have hk1 : (((5 : ℕ) + 1).primeFactors.erase 2).card ≤ 1 := by
    have h6 : ((5 + 1 : ℕ)).primeFactors = {2, 3} := by simp [Nat.primeFactors]
    rw [h6]
    decide
  by_cases hsp : s.Prime
  · exact OddPerfectNumber.no_dris_index_odd_prime_of_one_odd_prime p 5 m s hp hsp
      (by rintro rfl; exact hs_not_even (by decide)) (by norm_num) hm hpm hk1
  · exact OddPerfectNumber.no_dris_index_odd_composite_of_one_odd_prime p 5 m s hp (by norm_num)
      hm hpm hk1 (by omega) hs_not_even hsp
