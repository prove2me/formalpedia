-- Prove2me | solution 1 for OddPerfectNumber.even_orders_mod_53_q3_twentynine
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T06:50:04.58339+00:00
-- url     : https://prove2.me/submissions/032ef531-2f1b-4d51-9fb0-b60e9d30f51f

import Mathlib

set_option maxRecDepth 100000 in
theorem solution :
    Even (orderOf (3 : ZMod 53)) ∧
      Even (orderOf (5 : ZMod 53)) ∧
      Even (orderOf (29 : ZMod 53)) := by
  have h3nz : (3 : ZMod 53) ≠ 0 := by decide
  have h3one : (3 : ZMod 53) ≠ 1 := by decide
  have h3pow : (3 : ZMod 53) ^ 13 ≠ 1 := by decide
  have h5nz : (5 : ZMod 53) ≠ 0 := by decide
  have h5one : (5 : ZMod 53) ≠ 1 := by decide
  have h5pow : (5 : ZMod 53) ^ 13 ≠ 1 := by decide
  have h29nz : (29 : ZMod 53) ≠ 0 := by decide
  have h29one : (29 : ZMod 53) ≠ 1 := by decide
  have h29pow : (29 : ZMod 53) ^ 13 ≠ 1 := by decide
  letI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
  have heven : ∀ q : Nat, (q : ZMod 53) ≠ 0 →
      (q : ZMod 53) ≠ 1 → (q : ZMod 53) ^ 13 ≠ 1 →
      Even (orderOf (q : ZMod 53)) := by
    intro q hq0 hq1 hqpow
    have hdvd : orderOf (q : ZMod 53) ∣ 52 := by
      simpa using ZMod.orderOf_dvd_card_sub_one hq0
    rw [show (52 : Nat) = 2 ^ 2 * 13 by norm_num] at hdvd
    by_contra hne
    rw [Nat.not_even_iff_odd] at hne
    have hcop2 : Nat.Coprime (orderOf (q : ZMod 53)) 2 :=
      hne.coprime_two_right
    have hcop4 : Nat.Coprime (orderOf (q : ZMod 53)) (2 ^ 2) :=
      (Nat.coprime_pow_right_iff (show 0 < 2 by norm_num)
        (orderOf (q : ZMod 53)) 2).mpr hcop2
    have h13dvd : orderOf (q : ZMod 53) ∣ 13 :=
      (hcop4.dvd_mul_left).mp hdvd
    obtain ⟨t, ht⟩ := h13dvd
    have hpow := pow_orderOf_eq_one (q : ZMod 53)
    have hqpow' : (q : ZMod 53) ^ 13 = 1 := by
      rw [ht, pow_mul, hpow, one_pow]
    exact hqpow hqpow'
  exact ⟨heven 3 h3nz h3one h3pow,
    heven 5 h5nz h5one h5pow,
    heven 29 h29nz h29one h29pow⟩
