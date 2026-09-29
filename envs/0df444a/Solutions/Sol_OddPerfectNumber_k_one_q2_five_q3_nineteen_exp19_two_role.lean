-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_two_role
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T22:57:47.817145+00:00
-- url     : https://prove2.me/submissions/7b6ffbb3-2923-4b6f-b714-e6cfacf7e270

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19exp : (m ^ 2).factorization 19 = 2) :
    p = 127 ∨ q4 = 127 := by
  have hm0 : m ≠ 0 := by
    rcases hm with ⟨k, hk⟩
    omega
  have hn0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hlocal := OddPerfectNumber.local_sigma_factor_dvd_global
    (m ^ 2) 19 hn0 h19mem
  rw [h19exp] at hlocal
  have hlocal2 : (∑ i ∈ Finset.range (2 + 1), 19 ^ i) ∣
      ∑ x ∈ (m ^ 2).divisors, x := hlocal
  have h127local : 127 ∣ ∑ i ∈ Finset.range (2 + 1), 19 ^ i := by
    norm_num [Finset.sum_range_succ]
  have h127global : 127 ∣ ∑ x ∈ (m ^ 2).divisors, x :=
    dvd_trans h127local hlocal2
  have hddvd : d ∣ m ^ 2 := by
    refine ⟨(p + 1) / 2, ?_⟩
    simpa [Nat.mul_comm] using hprod
  have hcases := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 19 q4 127 hp (by norm_num) hm0 hsig hddvd h127global hsupport
  rcases hcases with h | h | h | h | h
  · exact Or.inl h.symm
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · exact Or.inr h.symm
