-- Prove2me | solution 1 for OddPerfectNumber.k_one_sigma_prime_mod_four_three_dvd_m
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T13:59:11.382471+00:00
-- url     : https://prove2.me/submissions/7201e260-bd9a-4e57-9a07-768129176d9a

import Mathlib
import Theorems.Thm_OddPerfectNumber_sigma_prime_mem_support_or_euler

theorem solution (p m d r : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hr : r.Prime) (hr4 : r % 4 = 3)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hrsigma : r ∣ (∑ x ∈ (m ^ 2).divisors, x)) :
    r ∣ m := by
  rcases OddPerfectNumber.sigma_prime_mem_support_or_euler
      p m d r hp hr hsig hddvd hrsigma with h | h
  · subst r
    omega
  · exact h
