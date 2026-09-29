-- Prove2me | solution 1 for OddPerfectNumber.four_support_external_eleven_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T18:36:58.608958+00:00
-- url     : https://prove2.me/submissions/0ab20ce6-eb96-4509-b582-1378c14c4d6f

import Mathlib
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 13 < q4)
    (h11sigma : 11 ∣ ∑ x ∈ (m ^ 2).divisors, x) :
    False := by
  have hcases := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 13 q4 11 hp (by norm_num) hm0 hsig hddvd h11sigma hsupport
  rcases hcases with h | h | h | h | h
  · subst p
    norm_num at hp4
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · omega
