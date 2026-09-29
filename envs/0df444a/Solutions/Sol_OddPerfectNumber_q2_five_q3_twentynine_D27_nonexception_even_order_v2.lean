-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_D27_nonexception_even_order_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T14:25:59.989648+00:00
-- url     : https://prove2.me/submissions/0c8575ea-3c42-48f3-94b1-897629ab1fba

import Mathlib

theorem solution (q4 : Nat)
    (hcases : q4 = 31 ∨ q4 = 37 ∨ q4 = 41 ∨ q4 = 43 ∨
      q4 = 59 ∨ q4 = 61 ∨ q4 = 67 ∨ q4 = 71 ∨ q4 = 73 ∨
      q4 = 79 ∨ q4 = 83) :
    Even (orderOf (q4 : ZMod 53)) := by
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
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h
  all_goals subst q4 <;> apply heven <;> decide
