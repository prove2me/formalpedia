-- Prove2me | solution 1 for OddPerfectNumber.even_order_three_mod_113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T12:43:32.999623+00:00
-- url     : https://prove2.me/submissions/54bb2038-d0dc-4326-afc5-9eaa539f23bb

import Mathlib

theorem solution : Even (orderOf (3 : ZMod 113)) := by
  have h7 : (3 : ZMod 113) ^ 7 ≠ 1 := by decide
  have h1 : (3 : ZMod 113) ≠ 1 := by decide
  letI : Fact (Nat.Prime 113) := ⟨by norm_num⟩
  have hne0 : (3 : ZMod 113) ≠ 0 := by
    intro hz
    have hmod := (ZMod.natCast_eq_natCast_iff' 3 0 113).mp hz
    norm_num at hmod
  have hdvd : orderOf (3 : ZMod 113) ∣ 112 := by
    simpa using ZMod.orderOf_dvd_card_sub_one hne0
  rw [show (112 : Nat) = 16 * 7 by norm_num] at hdvd
  by_contra hne
  rw [Nat.not_even_iff_odd] at hne
  have hcop2 : Nat.Coprime (orderOf (3 : ZMod 113)) 2 := hne.coprime_two_right
  have hcop16 : Nat.Coprime (orderOf (3 : ZMod 113)) (2 ^ 4) :=
    (Nat.coprime_pow_right_iff (show 0 < 4 by norm_num) _ _).mpr hcop2
  have h16 : (2 : Nat) ^ 4 = 16 := by norm_num
  rw [h16] at hcop16
  have h7dvd : orderOf (3 : ZMod 113) ∣ 7 :=
    (hcop16.dvd_mul_left).mp hdvd
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h7dvd with h | h
  · have hpow := pow_orderOf_eq_one (3 : ZMod 113)
    rw [h] at hpow
    simp at hpow
    exact h1 hpow
  · have hpow := pow_orderOf_eq_one (3 : ZMod 113)
    rw [h] at hpow
    exact h7 hpow
