-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_six_guarded_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T10:04:07.848749+00:00
-- url     : https://prove2.me/submissions/4dcedda3-e013-443a-922e-7349b925f9e9

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hm0 : m ≠ 0)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 6) :
    q4 = 1093 ∨ p = 1093 := by
  have h1093 : Nat.Prime 1093 := by norm_num
  have hS : (∑ i ∈ Finset.range (6 + 1), 3 ^ i) = 1093 := by norm_num
  have hloc : (∑ i ∈ Finset.range ((m ^ 2).factorization 3 + 1), 3 ^ i) ∣
      ∑ x ∈ (m ^ 2).divisors, x :=
    OddPerfectNumber.local_sigma_factor_dvd_global (m ^ 2) 3 (pow_ne_zero 2 hm0) h3mem
  rw [h3exp] at hloc
  have h1093dvd : 1093 ∣ ∑ x ∈ (m ^ 2).divisors, x := by
    have h : (∑ i ∈ Finset.range (6 + 1), 3 ^ i) ∣ ∑ x ∈ (m ^ 2).divisors, x := hloc
    rwa [hS] at h
  have hcases := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 19 q4 1093 hp h1093 hm0 hsig hddvd h1093dvd hsupport
  rcases hcases with h | h | h | h | h
  · exact Or.inr h.symm
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · exact Or.inl h.symm
