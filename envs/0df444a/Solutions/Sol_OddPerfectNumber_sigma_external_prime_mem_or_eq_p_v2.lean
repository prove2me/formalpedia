-- Prove2me | solution 1 for OddPerfectNumber.sigma_external_prime_mem_or_eq_p_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T01:22:51.99241+00:00
-- url     : https://prove2.me/submissions/07a5c328-9475-4ad7-af5e-620d8f452bb9

import Mathlib

theorem solution (p m d sigma r : Nat)
    (hp : p.Prime)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hr : r.Prime)
    (hdiv : r ∣ sigma) :
    r ∣ m ∨ r = p := by
  have hsd : sigma = p * d := by rw [hglobal, hsig]
  rw [hsd] at hdiv
  rcases hr.dvd_mul.mp hdiv with h | h
  · right
    exact (Nat.prime_dvd_prime_iff_eq hr hp).mp h
  · left
    have hdvd : d ∣ m ^ 2 := ⟨(p + 1) / 2, by rw [hprod, Nat.mul_comm]⟩
    have h2 : r ∣ m ^ 2 := dvd_trans h hdvd
    exact hr.dvd_of_dvd_pow h2
