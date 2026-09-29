-- Prove2me | solution 1 for OddPerfectNumber.even_order_31_mod_53_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T05:21:44.18767+00:00
-- url     : https://prove2.me/submissions/e9e335f5-0f9c-40fc-b540-cef5a83938e7

import Mathlib

theorem solution : Even (orderOf (31 : ZMod 53)) := by
  have h52 : (31 : ZMod 53) ^ 52 = 1 := by decide
  have h26 : (31 : ZMod 53) ^ 26 ≠ 1 := by decide
  have hdvd52 : orderOf (31 : ZMod 53) ∣ 52 :=
    orderOf_dvd_of_pow_eq_one h52
  by_contra hne
  rw [Nat.not_even_iff_odd] at hne
  have hcop : Nat.Coprime (orderOf (31 : ZMod 53)) 2 :=
    hne.coprime_two_right
  have h52' : orderOf (31 : ZMod 53) ∣ 2 * 26 := hdvd52
  have hdvd26 : orderOf (31 : ZMod 53) ∣ 26 :=
    Nat.Coprime.dvd_of_dvd_mul_left hcop h52'
  rw [orderOf_dvd_iff_pow_eq_one] at hdvd26
  exact h26 hdvd26
