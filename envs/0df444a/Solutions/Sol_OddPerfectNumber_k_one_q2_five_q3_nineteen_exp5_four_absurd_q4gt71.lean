-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_four_absurd_q4gt71
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T22:10:36.949544+00:00
-- url     : https://prove2.me/submissions/6807679a-be2b-4bfd-8504-712aca06368b

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 71 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 4) :
    False := by
  have hm0 : m ≠ 0 := by
    rcases hm with ⟨k, hk⟩
    omega
  have hn0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hlocal := OddPerfectNumber.local_sigma_factor_dvd_global
    (m ^ 2) 5 hn0 h5mem
  rw [h5exp] at hlocal
  have hlocal4 : (∑ i ∈ Finset.range (4 + 1), 5 ^ i) ∣
      ∑ x ∈ (m ^ 2).divisors, x := hlocal
  have h11local : 11 ∣ ∑ i ∈ Finset.range (4 + 1), 5 ^ i := by
    norm_num [Finset.sum_range_succ]
  have h11global : 11 ∣ ∑ x ∈ (m ^ 2).divisors, x :=
    dvd_trans h11local hlocal4
  have hddvd : d ∣ m ^ 2 := by
    refine ⟨(p + 1) / 2, ?_⟩
    simpa [Nat.mul_comm] using hprod
  have hcases := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 19 q4 11 hp (by norm_num) hm0 hsig hddvd h11global hsupport
  rcases hcases with h | h | h | h | h
  · subst p
    norm_num at hp4
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · omega
