-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_two_role
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T21:51:54.947318+00:00
-- url     : https://prove2.me/submissions/53d0d77c-5479-4c92-82ac-5d36b8576285

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2) :
    p = 13 := by
  have hm0 : m ≠ 0 := by
    rcases hm with ⟨k, hk⟩
    omega
  have hn0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hlocal := OddPerfectNumber.local_sigma_factor_dvd_global
    (m ^ 2) 3 hn0 h3mem
  rw [h3exp] at hlocal
  have hlocal2 : (∑ i ∈ Finset.range (2 + 1), 3 ^ i) ∣
      ∑ x ∈ (m ^ 2).divisors, x := hlocal
  have h13local : 13 ∣ ∑ i ∈ Finset.range (2 + 1), 3 ^ i := by
    norm_num [Finset.sum_range_succ]
  have h13global : 13 ∣ ∑ x ∈ (m ^ 2).divisors, x :=
    dvd_trans h13local hlocal2
  have hddvd : d ∣ m ^ 2 := by
    refine ⟨(p + 1) / 2, ?_⟩
    simpa [Nat.mul_comm] using hprod
  have hcases := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 19 q4 13 hp (by norm_num) hm0 hsig hddvd h13global hsupport
  rcases hcases with h | h | h | h | h
  · exact h.symm
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · have : 19 < 13 := by simpa [h]
    omega
