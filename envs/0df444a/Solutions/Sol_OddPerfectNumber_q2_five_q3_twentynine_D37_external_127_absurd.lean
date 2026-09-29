-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_D37_external_127_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T08:09:36.192919+00:00
-- url     : https://prove2.me/submissions/2c070b72-aed4-46cf-bc10-3d8905e25cd9

import Mathlib
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4eq : q4 = 37)
    (h127sigma : 127 ∣ ∑ x ∈ (m ^ 2).divisors, x) :
    False := by
  have h := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 29 q4 127 hp (by norm_num) hm0 hsig hddvd h127sigma hsupport
  rcases h with h | h | h | h | h
  · subst p
    norm_num at hp4
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · subst q4
    norm_num at h
