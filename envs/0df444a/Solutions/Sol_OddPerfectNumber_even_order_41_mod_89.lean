-- Prove2me | solution 1 for OddPerfectNumber.even_order_41_mod_89
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T22:41:57.323302+00:00
-- url     : https://prove2.me/submissions/4d50a759-9597-47de-afff-e13fd3ade0dc

import Mathlib

set_option maxRecDepth 100000 in
theorem solution : Even (orderOf (41 : ZMod 89)) := by
  have h0 : (41 : ZMod 89) ≠ 0 := by decide
  have h1 : (41 : ZMod 89) ≠ 1 := by decide
  have hpow : (41 : ZMod 89) ^ 11 ≠ 1 := by decide
  letI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  have hdvd : orderOf (41 : ZMod 89) ∣ 88 := by
    simpa using ZMod.orderOf_dvd_card_sub_one h0
  rw [show (88 : Nat) = 2 ^ 3 * 11 by norm_num] at hdvd
  by_contra hne
  rw [Nat.not_even_iff_odd] at hne
  have hcop2 : Nat.Coprime (orderOf (41 : ZMod 89)) 2 :=
    hne.coprime_two_right
  have hcop8 : Nat.Coprime (orderOf (41 : ZMod 89)) (2 ^ 3) :=
    (Nat.coprime_pow_right_iff (show 0 < 3 by norm_num)
      (orderOf (41 : ZMod 89)) 2).mpr hcop2
  have h11dvd : orderOf (41 : ZMod 89) ∣ 11 :=
    (hcop8.dvd_mul_left).mp hdvd
  obtain ⟨t, ht⟩ := h11dvd
  have hpow0 := pow_orderOf_eq_one (41 : ZMod 89)
  have hpow' : (41 : ZMod 89) ^ 11 = 1 := by
    rw [ht, pow_mul, hpow0, one_pow]
  exact hpow hpow'
