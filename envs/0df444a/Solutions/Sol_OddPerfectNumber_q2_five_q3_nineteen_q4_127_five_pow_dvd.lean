-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_127_five_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T02:03:34.138393+00:00
-- url     : https://prove2.me/submissions/950c6ca4-10ba-4ef2-843c-d7bc8ff61be8

import Mathlib

theorem solution (m a b c e : Nat)
    (hfac : m ^ 2 = 3 ^ a * 5 ^ b * 19 ^ c * 127 ^ e)
    (hb : 6 ≤ b) :
    5 ^ 6 ∣ m ^ 2 := by
  rw [hfac]
  have hpow : 5 ^ 6 ∣ 5 ^ b := pow_dvd_pow 5 hb
  have hmid : 5 ^ 6 ∣ 5 ^ b * 19 ^ c := dvd_mul_of_dvd_left hpow _
  have hall : 5 ^ 6 ∣ (5 ^ b * 19 ^ c) * 127 ^ e :=
    dvd_mul_of_dvd_left hmid _
  have hfull : 5 ^ 6 ∣ 3 ^ a * ((5 ^ b * 19 ^ c) * 127 ^ e) :=
    dvd_mul_of_dvd_right hall _
  simpa [mul_assoc] using hfull
