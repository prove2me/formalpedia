-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_61_external_131_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T19:27:57.166868+00:00
-- url     : https://prove2.me/submissions/bc6dba6c-71cf-4f34-be83-75e943e0a9a7

import Mathlib
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 23 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4eq : q4 = 61)
    (h131sigma : 131 ∣ ∑ x ∈ (m ^ 2).divisors, x) :
    False := by
  have h := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 23 q4 131 hp (by norm_num) hm0 hsig hddvd h131sigma hsupport
  rcases h with h | h | h | h | h
  · subst p
    norm_num at hp4
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · subst q4
    norm_num at h
