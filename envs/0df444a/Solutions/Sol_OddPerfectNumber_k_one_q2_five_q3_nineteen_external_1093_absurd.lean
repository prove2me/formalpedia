-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_external_1093_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T21:32:16.072648+00:00
-- url     : https://prove2.me/submissions/ff919fef-5df3-4342-a5bb-3aeac327ecdf

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 1093 < q4)
    (hpne : p ≠ 1093)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 6) :
    False := by
  have hm0 : m ≠ 0 := by
    rcases hm with ⟨k, hk⟩
    omega
  have hn0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hlocal := OddPerfectNumber.local_sigma_factor_dvd_global
    (m ^ 2) 3 hn0 h3mem
  rw [h3exp] at hlocal
  have hlocal6 : (∑ i ∈ Finset.range (6 + 1), 3 ^ i) ∣
      ∑ x ∈ (m ^ 2).divisors, x := hlocal
  have h1093local : 1093 ∣ ∑ i ∈ Finset.range (6 + 1), 3 ^ i := by
    norm_num [Finset.sum_range_succ]
  have h1093global : 1093 ∣ ∑ x ∈ (m ^ 2).divisors, x :=
    dvd_trans h1093local hlocal6
  have hcases := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 19 q4 1093 hp (by norm_num) hm0 hsig hddvd h1093global hsupport
  rcases hcases with h | h | h | h | h
  · exact hpne h.symm
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · omega
