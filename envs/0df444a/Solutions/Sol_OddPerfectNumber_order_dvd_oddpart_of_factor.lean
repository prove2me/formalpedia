-- Prove2me | solution 1 for OddPerfectNumber.order_dvd_oddpart_of_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T13:34:50.54528+00:00
-- url     : https://prove2.me/submissions/27cfc8cb-eef8-42a4-965e-373df3046f73

import Mathlib

theorem solution {p q k u : Nat}
    (hfactor : p - 1 = 2 ^ k * u)
    (hord : orderOf (q : ZMod p) ∣ p - 1)
    (hodd : Odd (orderOf (q : ZMod p))) :
    orderOf (q : ZMod p) ∣ u := by
  rw [hfactor] at hord
  exact (hodd.coprime_two_right.pow_right k).dvd_of_dvd_mul_left hord
