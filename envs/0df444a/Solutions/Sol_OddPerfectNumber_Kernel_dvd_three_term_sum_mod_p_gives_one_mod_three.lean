-- Prove2me | solution 1 for OddPerfectNumber.Kernel.dvd_three_term_sum_mod_p_gives_one_mod_three
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T15:18:03.912409+00:00
-- url     : https://prove2.me/submissions/7de424c5-ae4b-444e-8c61-6a6e07a1a872

import Mathlib

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

theorem solution {p t : Nat} (hp : p.Prime) (hp5 : 5 ≤ p) (ht1 : t % p ≠ 1)
    (h : Dvd.dvd p (1 + t + t ^ 2)) : p % 3 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have _ := hp5
  let a : ZMod p := t
  have hsum : a ^ 2 + a + 1 = 0 := by
    have h0 : ((1 + t + t ^ 2 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (1 + t + t ^ 2) p).2 h
    have h1 : (1 : ZMod p) + a + a ^ 2 = 0 := by
      simpa [a, Nat.cast_add, Nat.cast_pow, Nat.cast_one] using h0
    rw [show a ^ 2 + a + 1 = (1 : ZMod p) + a + a ^ 2 by ring]
    exact h1
  have hcube : a ^ 3 = 1 := by
    have hfac : a ^ 3 - 1 = (a - 1) * (a ^ 2 + a + 1) := by ring
    rw [hsum] at hfac
    have : a ^ 3 - 1 = 0 := by simpa using hfac
    exact sub_eq_zero.mp this
  have ha1 : a ≠ 1 := by
    intro ha
    have : t % p = 1 % p :=
      (ZMod.natCast_eq_natCast_iff' t 1 p).1 (by simpa [a] using ha)
    rw [Nat.mod_eq_of_lt (Nat.Prime.one_lt hp)] at this
    exact ht1 this
  have ha0 : a ≠ 0 := by
    intro h0
    simp [h0] at hsum
  have hfermat : a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha0
  have hdiv3 : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one hcube
  have hord : orderOf a = 3 := by
    have hne : orderOf a ≠ 1 := fun h1 => ha1 ((orderOf_eq_one_iff).1 h1)
    rcases (Nat.dvd_prime Nat.prime_three).1 hdiv3 with h | h
    · exact (hne h).elim
    · exact h
  have h3 : 3 ∣ p - 1 := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hfermat
  obtain ⟨k, hk⟩ := h3
  have hp1 : p = 3 * k + 1 := by omega
  rw [hp1, Nat.mul_add_mod_self_left]
