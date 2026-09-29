-- Prove2me | solution 3 for OddPerfectNumber.no_dris_thirteen_s_ge_two_not_even
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T11:55:11.42009+00:00
-- url     : https://prove2.me/submissions/08c8f5dc-114d-45aa-a930-34b18e0c8100
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_dris_thirteen_s_ge_two_two_odd_primes
import Theorems.Thm_OddPerfectNumber_no_dris_index_odd_prime_of_one_odd_prime
import Theorems.Thm_OddPerfectNumber_no_dris_index_odd_composite_of_one_odd_prime

theorem _root_.solution (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk13 : 13 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  have hk0 : k ≠ 0 := by omega
  have hsne2 : s ≠ 2 := by
    intro h; exact hs_not_even (by rw [h]; exact even_two)
  by_cases hcard : 2 ≤ ((k + 1).primeFactors.erase 2).card
  · exact OddPerfectNumber.no_dris_thirteen_s_ge_two_two_odd_primes p k m s hp hp2 hp4 hk4
      hk13 hm hpm hs2 hs_not_even hcard
  · push_neg at hcard
    have hcard1 : ((k + 1).primeFactors.erase 2).card ≤ 1 := by omega
    by_cases hsp : s.Prime
    · exact OddPerfectNumber.no_dris_index_odd_prime_of_one_odd_prime p k m s hp hsp hsne2
        hk0 hm hpm hcard1
    · exact OddPerfectNumber.no_dris_index_odd_composite_of_one_odd_prime p k m s hp hk0 hm
        hpm hcard1 hs2 hs_not_even hsp

#print axioms solution
