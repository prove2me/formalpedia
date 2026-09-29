-- Prove2me | solution 4 for OddPerfectNumber.no_dris_thirteen_s_ge_two_not_even
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:10.850672+00:00
-- url     : https://prove2.me/submissions/6eee4672-202b-4700-a26f-bf97e9fe46ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_dris_thirteen_s_ge_two_two_odd_primes
import Theorems.Thm_OddPerfectNumber_no_dris_index_odd_prime_of_one_odd_prime
import Theorems.Thm_OddPerfectNumber_no_dris_one_odd_prime_core

theorem _root_.solution (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk13 : 13 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  intro h
  have hk : k ≠ 0 := by omega
  by_cases hc : 2 ≤ ((k + 1).primeFactors.erase 2).card
  · exact OddPerfectNumber.no_dris_thirteen_s_ge_two_two_odd_primes p k m s hp hp2 hp4 hk4
      hk13 hm hpm hs2 hs_not_even hc h
  · have hc1 : ((k + 1).primeFactors.erase 2).card ≤ 1 := by omega
    by_cases hsp : s.Prime
    · have hsne : s ≠ 2 := by
        rintro rfl; exact hs_not_even (by norm_num)
      exact OddPerfectNumber.no_dris_index_odd_prime_of_one_odd_prime p k m s hp hsp hsne hk
        hm hpm hc1 h
    · have hs_dvd : s ∣ m ^ 2 := by
        have hodd : Odd s := (Nat.even_or_odd s).resolve_left hs_not_even
        have hcop : Nat.Coprime s 2 := Nat.coprime_two_right.2 hodd
        have hd2 : s ∣ m ^ 2 * 2 :=
          ⟨∑ d ∈ (p ^ k).divisors, d, by rw [mul_comm (m ^ 2) 2, h.1]; ring⟩
        exact Nat.Coprime.dvd_of_dvd_mul_right hcop hd2
      exact OddPerfectNumber.no_dris_one_odd_prime_core p k m s hp hk hm hpm hc1 hs2
        hs_not_even hsp hs_dvd h
