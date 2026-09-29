-- Prove2me | solution 1 for OddPerfectNumber.orders_mod_1709_even_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T03:43:09.001664+00:00
-- url     : https://prove2.me/submissions/6310627f-f469-408a-a0fc-b5c6d9609867

import Mathlib

set_option maxRecDepth 100000 in
theorem solution :
    Even (orderOf (3 : ZMod 1709)) ∧
    Even (orderOf (5 : ZMod 1709)) ∧
    Even (orderOf (19 : ZMod 1709)) ∧
    Even (orderOf (101 : ZMod 1709)) := by
  have h3nz : (3 : ZMod 1709) ≠ 0 := by decide
  have h3one : (3 : ZMod 1709) ≠ 1 := by decide
  have h3pow : (3 : ZMod 1709) ^ 427 ≠ 1 := by decide
  have h5nz : (5 : ZMod 1709) ≠ 0 := by decide
  have h5one : (5 : ZMod 1709) ≠ 1 := by decide
  have h5pow : (5 : ZMod 1709) ^ 427 ≠ 1 := by decide
  have h19nz : (19 : ZMod 1709) ≠ 0 := by decide
  have h19one : (19 : ZMod 1709) ≠ 1 := by decide
  have h19pow : (19 : ZMod 1709) ^ 427 ≠ 1 := by decide
  have h101nz : (101 : ZMod 1709) ≠ 0 := by decide
  have h101one : (101 : ZMod 1709) ≠ 1 := by decide
  have h101pow : (101 : ZMod 1709) ^ 427 ≠ 1 := by decide
  letI : Fact (Nat.Prime 1709) := ⟨by norm_num⟩
  have heven : ∀ q : Nat, (q : ZMod 1709) ≠ 0 →
      (q : ZMod 1709) ≠ 1 → (q : ZMod 1709) ^ 427 ≠ 1 →
      Even (orderOf (q : ZMod 1709)) := by
    intro q hq0 hq1 hqpow
    have hdvd : orderOf (q : ZMod 1709) ∣ 1708 := by
      simpa using ZMod.orderOf_dvd_card_sub_one hq0
    rw [show (1708 : Nat) = 2 ^ 2 * 427 by norm_num] at hdvd
    by_contra hne
    rw [Nat.not_even_iff_odd] at hne
    have hcop2 : Nat.Coprime (orderOf (q : ZMod 1709)) 2 :=
      hne.coprime_two_right
    have hcop4 : Nat.Coprime (orderOf (q : ZMod 1709)) (2 ^ 2) :=
      (Nat.coprime_pow_right_iff (show 0 < 2 by norm_num) _ _).mpr hcop2
    have h4 : (2 : Nat) ^ 2 = 4 := by norm_num
    rw [h4] at hcop4
    have h427dvd : orderOf (q : ZMod 1709) ∣ 427 :=
      (hcop4.dvd_mul_left).mp hdvd
    obtain ⟨t, ht⟩ := h427dvd
    have hpow := pow_orderOf_eq_one (q : ZMod 1709)
    have hqpow' : (q : ZMod 1709) ^ 427 = 1 := by
      rw [ht, pow_mul, hpow, one_pow]
    exact hqpow hqpow'
  have h3 := heven 3 h3nz h3one h3pow
  have h5 := heven 5 h5nz h5one h5pow
  have h19 := heven 19 h19nz h19one h19pow
  have h101 := heven 101 h101nz h101one h101pow
  exact ⟨h3, h5, h19, h101⟩
