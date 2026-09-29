-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_127_five_dvd_sigma_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T06:28:09.527156+00:00
-- url     : https://prove2.me/submissions/b312c5cb-e716-44f5-850d-f69d81f302d3

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_five_dvd_sigma_v4

theorem solution (p m d sigma : Nat)
    (hp : p.Prime)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsigma : sigma = p * d)
    (hD : (p + 1) / 2 < 185)
    (hpow : 5 ^ 6 ∣ m ^ 2) :
    5 ∣ sigma := by
  exact OddPerfectNumber.q2_five_q3_nineteen_q4_127_five_dvd_sigma_v4
    p m d sigma hp hprod hsigma hD hpow
