-- Prove2me | solution 1 for OddPerfectNumber.even_order_31_mod_61
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T12:12:02.283723+00:00
-- url     : https://prove2.me/submissions/f594205c-428c-46ef-bdbc-9523d64830f7

import Mathlib

set_option maxRecDepth 100000 in
theorem solution : Even (orderOf (31 : ZMod 61)) := by
  have hnz : (31 : ZMod 61) ≠ 0 := by decide
  have hone : (31 : ZMod 61) ≠ 1 := by decide
  have hpow_ne : (31 : ZMod 61) ^ 15 ≠ 1 := by decide
  letI : Fact (Nat.Prime 61) := ⟨by norm_num⟩
  have hdvd : orderOf (31 : ZMod 61) ∣ 60 := by
    simpa using ZMod.orderOf_dvd_card_sub_one hnz
  rw [show (60 : Nat) = 2 ^ 2 * 15 by norm_num] at hdvd
  by_contra hne
  rw [Nat.not_even_iff_odd] at hne
  have hcop2 : Nat.Coprime (orderOf (31 : ZMod 61)) 2 :=
    hne.coprime_two_right
  have hcop4 : Nat.Coprime (orderOf (31 : ZMod 61)) (2 ^ 2) :=
    (Nat.coprime_pow_right_iff (show 0 < 2 by norm_num) _ _).mpr hcop2
  have h15dvd : orderOf (31 : ZMod 61) ∣ 15 :=
    (hcop4.dvd_mul_left).mp hdvd
  obtain ⟨t, ht⟩ := h15dvd
  have hpow := pow_orderOf_eq_one (31 : ZMod 61)
  have hpow' : (31 : ZMod 61) ^ 15 = 1 := by
    rw [ht, pow_mul, hpow, one_pow]
  exact hpow_ne hpow'
