-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_D15_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T05:08:09.525144+00:00
-- url     : https://prove2.me/submissions/1e700ceb-c7a0-4f90-990e-238380924128

import Mathlib

theorem solution (p m d q4 a b c e sigma D : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (h29mem : 29 ∈ (m ^ 2).primeFactors)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (hp_eq : p = 2 * D - 1) (hD : D = 15) :
    False := by
  subst hD
  have hp29 : p = 29 := by omega
  subst hp29
  have hdvd : 29 ∣ m ^ 2 := ((Nat.mem_primeFactors.mp h29mem).2).1
  exact hpm (Nat.Prime.dvd_of_dvd_pow hp hdvd)
