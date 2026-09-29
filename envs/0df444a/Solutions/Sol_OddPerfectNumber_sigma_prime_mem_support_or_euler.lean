-- Prove2me | solution 1 for OddPerfectNumber.sigma_prime_mem_support_or_euler
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T10:16:47.764201+00:00
-- url     : https://prove2.me/submissions/3d979fa9-bcff-460e-9a49-e2fd57e6c8e6

import Mathlib

theorem solution (p m d r : Nat)
    (hp : p.Prime) (hr : r.Prime)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hrsigma : r ∣ ∑ x ∈ (m ^ 2).divisors, x) :
    r = p ∨ r ∣ m := by
  have hrdprod : r ∣ p * d := by
    rw [← hsig]
    exact hrsigma
  rcases (Nat.Prime.dvd_mul hr).mp hrdprod with hrp | hrd
  · left
    exact (Nat.prime_dvd_prime_iff_eq hr hp).mp hrp
  · right
    exact hr.dvd_of_dvd_pow (dvd_trans hrd hddvd)
