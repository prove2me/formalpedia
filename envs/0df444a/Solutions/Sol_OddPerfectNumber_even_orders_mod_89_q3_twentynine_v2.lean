-- Prove2me | solution 1 for OddPerfectNumber.even_orders_mod_89_q3_twentynine_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T06:36:40.376642+00:00
-- url     : https://prove2.me/submissions/383d57be-b793-445b-9036-364f0fb17c2c

import Mathlib

set_option maxRecDepth 100000 in
theorem solution :
    Even (orderOf (3 : ZMod 89)) ∧
      Even (orderOf (5 : ZMod 89)) ∧
      Even (orderOf (29 : ZMod 89)) := by
  have h3nz : (3 : ZMod 89) ≠ 0 := by decide
  have h3one : (3 : ZMod 89) ≠ 1 := by decide
  have h3pow : (3 : ZMod 89) ^ 11 ≠ 1 := by decide
  have h5nz : (5 : ZMod 89) ≠ 0 := by decide
  have h5one : (5 : ZMod 89) ≠ 1 := by decide
  have h5pow : (5 : ZMod 89) ^ 11 ≠ 1 := by decide
  have h29nz : (29 : ZMod 89) ≠ 0 := by decide
  have h29one : (29 : ZMod 89) ≠ 1 := by decide
  have h29pow : (29 : ZMod 89) ^ 11 ≠ 1 := by decide
  letI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  have heven : ∀ q : Nat, (q : ZMod 89) ≠ 0 →
      (q : ZMod 89) ≠ 1 → (q : ZMod 89) ^ 11 ≠ 1 →
      Even (orderOf (q : ZMod 89)) := by
    intro q hq0 hq1 hqpow
    have hdvd : orderOf (q : ZMod 89) ∣ 88 := by
      simpa using ZMod.orderOf_dvd_card_sub_one hq0
    rw [show (88 : Nat) = 2 ^ 3 * 11 by norm_num] at hdvd
    by_contra hne
    rw [Nat.not_even_iff_odd] at hne
    have hcop2 : Nat.Coprime (orderOf (q : ZMod 89)) 2 :=
      hne.coprime_two_right
    have hcop8 : Nat.Coprime (orderOf (q : ZMod 89)) (2 ^ 3) :=
      (Nat.coprime_pow_right_iff (show 0 < 3 by norm_num)
        (orderOf (q : ZMod 89)) 2).mpr hcop2
    have h11dvd : orderOf (q : ZMod 89) ∣ 11 :=
      (hcop8.dvd_mul_left).mp hdvd
    obtain ⟨t, ht⟩ := h11dvd
    have hpow := pow_orderOf_eq_one (q : ZMod 89)
    have hqpow' : (q : ZMod 89) ^ 11 = 1 := by
      rw [ht, pow_mul, hpow, one_pow]
    exact hqpow hqpow'
  exact ⟨heven 3 h3nz h3one h3pow,
    heven 5 h5nz h5one h5pow,
    heven 29 h29nz h29one h29pow⟩
