-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D27_external_source_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T03:51:19.01827+00:00
-- url     : https://prove2.me/submissions/d477a29e-6aaa-4348-adf6-bde0fbf0f6d8

import Mathlib
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

theorem solution (m d sigma q4 : Nat)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = 53 * d)
    (hddvd : d ∣ m ^ 2) (hm0 : m ≠ 0)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hcase :
      (q4 = 47 ∧ 2237 ∣ ∑ x ∈ (m ^ 2).divisors, x) ∨
      (q4 = 89 ∧ 79 ∣ ∑ x ∈ (m ^ 2).divisors, x)) :
    False := by
  rcases hcase with h47 | h89
  · rcases h47 with ⟨hq4, hdiv⟩
    have hres := OddPerfectNumber.four_support_sigma_prime_restricted
      53 m d 3 5 29 q4 2237 (by norm_num) (by norm_num) hm0
      hsig hddvd hdiv hsupport
    rcases hres with h | h | h | h | h <;> norm_num [hq4] at h
  · rcases h89 with ⟨hq4, hdiv⟩
    have hres := OddPerfectNumber.four_support_sigma_prime_restricted
      53 m d 3 5 29 q4 79 (by norm_num) (by norm_num) hm0
      hsig hddvd hdiv hsupport
    rcases hres with h | h | h | h | h <;> norm_num [hq4] at h
