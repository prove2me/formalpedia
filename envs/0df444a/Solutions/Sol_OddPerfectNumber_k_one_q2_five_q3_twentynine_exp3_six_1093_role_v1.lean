-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_exp3_six_1093_role_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T23:54:22.802668+00:00
-- url     : https://prove2.me/submissions/9c5e4625-1584-44d3-9208-7b3d58b3c044

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 6) :
    p = 1093 ∨ q4 = 1093 := by
  have hm0 : m ≠ 0 := by obtain ⟨k, hk⟩ := hm; omega
  have hsq0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hloc := OddPerfectNumber.local_sigma_factor_dvd_global (m ^ 2) 3 hsq0 h3mem
  rw [h3exp] at hloc
  have hSeq : (∑ i ∈ Finset.range (6 + 1), 3 ^ i) = 1093 := by
    norm_num [Finset.sum_range_succ]
  rw [hSeq] at hloc
  have hddvd : d ∣ m ^ 2 := ⟨(p + 1) / 2, by rw [hprod]; ring⟩
  have hcase := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 29 q4 1093 hp (by norm_num) hm0 hsig hddvd hloc hsupport
  rcases hcase with h | h | h | h | h
  · exact Or.inl h.symm
  · omega
  · omega
  · omega
  · exact Or.inr h.symm
