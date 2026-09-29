-- Prove2me | solution 3 for OddPerfectNumber.no_dris_nine_s_ge_two_not_even
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:51:49.294782+00:00
-- url     : https://prove2.me/submissions/b85dd0a6-f7dd-462b-8b71-54c9c0e905ff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_dris_two_odd_primes_core
import Theorems.Thm_OddPerfectNumber_no_dris_index_odd_prime_of_one_odd_prime
import Theorems.Thm_OddPerfectNumber_no_dris_one_odd_prime_core

theorem _root_.solution (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk9 : k = 9) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  intro h
  have hk : k ≠ 0 := by omega
  have hs_dvd : s ∣ m ^ 2 := by
    have hodd : Odd s := (Nat.even_or_odd s).resolve_left hs_not_even
    have hcop : Nat.Coprime s 2 := Nat.coprime_two_right.2 hodd
    have hd2 : s ∣ m ^ 2 * 2 :=
      ⟨∑ d ∈ (p ^ k).divisors, d, by rw [mul_comm (m ^ 2) 2, h.1]; ring⟩
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop hd2
  by_cases hc : 2 ≤ ((k + 1).primeFactors.erase 2).card
  · exact OddPerfectNumber.no_dris_two_odd_primes_core p k m s hp hk hm hpm hc hs2
      hs_not_even hs_dvd h
  · have hc1 : ((k + 1).primeFactors.erase 2).card ≤ 1 := by omega
    by_cases hsp : s.Prime
    · have hsne : s ≠ 2 := by rintro rfl; exact hs_not_even (by norm_num)
      exact OddPerfectNumber.no_dris_index_odd_prime_of_one_odd_prime p k m s hp hsp hsne hk
        hm hpm hc1 h
    · exact OddPerfectNumber.no_dris_one_odd_prime_core p k m s hp hk hm hpm hc1 hs2
        hs_not_even hsp hs_dvd h
