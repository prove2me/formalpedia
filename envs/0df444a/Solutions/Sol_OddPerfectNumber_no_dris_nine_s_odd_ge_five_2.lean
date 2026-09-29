-- Prove2me | solution 2 for OddPerfectNumber.no_dris_nine_s_odd_ge_five
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-11T09:05:53.984343+00:00
-- url     : https://prove2.me/submissions/77a5dbc6-eb2b-4a56-ad40-06bdce83f9a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_dris_index_odd_prime_of_one_odd_prime
import Theorems.Thm_OddPerfectNumber_no_dris_index_odd_composite_of_one_odd_prime

/-!
Reduction of `OddPerfectNumber.no_dris_nine_s_odd_ge_five`.

Since `k + 1 = 10` has the single odd prime divisor `5`, a prime index is excluded by
`OddPerfectNumber.no_dris_index_odd_prime_of_one_odd_prime`; the remaining case is an odd
composite index, which is the child lemma
`OddPerfectNumber.no_dris_index_odd_composite_of_one_odd_prime`.
-/

open Finset

theorem solution (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk9 : k = 9) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs5 : 5 ≤ s) (hs_not_even : ¬ Even s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  subst hk9
  have hk1 : (((9 : ℕ) + 1).primeFactors.erase 2).card ≤ 1 := by
    have h10 : ((9 + 1 : ℕ)).primeFactors = {2, 5} := by simp [Nat.primeFactors]
    rw [h10]
    decide
  by_cases hsp : s.Prime
  · exact OddPerfectNumber.no_dris_index_odd_prime_of_one_odd_prime p 9 m s hp hsp
      (by rintro rfl; exact hs_not_even (by decide)) (by norm_num) hm hpm hk1
  · exact OddPerfectNumber.no_dris_index_odd_composite_of_one_odd_prime p 9 m s hp (by norm_num)
      hm hpm hk1 (by omega) hs_not_even hsp
