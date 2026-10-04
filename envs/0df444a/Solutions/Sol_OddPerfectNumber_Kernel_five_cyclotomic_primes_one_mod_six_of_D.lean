-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_cyclotomic_primes_one_mod_six_of_D
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T15:33:50.637566+00:00
-- url     : https://prove2.me/submissions/c01d4218-c5d6-4194-95f0-0459b714a042

import Mathlib

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

theorem solution {p q : Nat} (hp : Nat.Prime p) (hp3 : p != 3) (hq : Nat.Prime q) (hq3 : q != 3)
    (hqd : q ∣ p ^ 2 - p + 1) : q % 6 = 1 := by
  have _ := hp3
  haveI : Fact q.Prime := ⟨hq⟩
  have hq_ne3 : q ≠ 3 := by simpa [bne_iff_ne] using hq3
  have he : Even (p * (p - 1)) := by
    rcases Nat.even_or_odd p with hpE | hpO
    · exact hpE.mul_right (p - 1)
    · obtain ⟨k, hk⟩ := hpO
      have : p - 1 = 2 * k := by omega
      rw [this]
      exact (even_two_mul k).mul_left p
  have hid : p ^ 2 - p + 1 = p * (p - 1) + 1 := by
    have hmul : p * (p - 1) = p * p - p := by
      simpa [Nat.mul_one] using (Nat.mul_sub_left_distrib p p 1)
    have : p * (p - 1) = p ^ 2 - p := by simpa [Nat.pow_two] using hmul
    omega
  have hq_ne2 : q ≠ 2 := by
    intro h2
    have h0 : (p ^ 2 - p + 1) % 2 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp (by simpa [h2] using hqd)
    have h1 : (p ^ 2 - p + 1) % 2 = 1 := by
      rw [hid, Nat.add_mod, Nat.even_iff.mp he, Nat.zero_add, Nat.mod_mod, Nat.one_mod]
    omega
  let a : ZMod q := p
  have hpoly : a ^ 2 - a + 1 = 0 := by
    have hle : p ≤ p ^ 2 := by rw [Nat.pow_two]; exact Nat.le_mul_self p
    have h0 : ((p ^ 2 - p + 1 : ℕ) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff (p ^ 2 - p + 1) q).2 hqd
    have hcast : a ^ 2 - a + 1 = ((p ^ 2 - p + 1 : ℕ) : ZMod q) := by
      simp [a, Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow, Nat.cast_one]
    rw [hcast]
    exact h0
  have ha_ne_neg : a ≠ -1 := by
    intro ha
    have h3 : (3 : ZMod q) = 0 := by
      have : a ^ 2 - a + 1 = 3 := by rw [ha]; ring
      exact this.symm.trans hpoly
    have hd3 : q ∣ 3 := (ZMod.natCast_eq_zero_iff 3 q).1 (by simpa using h3)
    exact hq_ne3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 hd3)
  have hcube : a ^ 3 = -1 := by
    have hfac : (a + 1) * (a ^ 2 - a + 1) = a ^ 3 + 1 := by ring
    have : a ^ 3 + 1 = 0 := by simpa [hpoly] using hfac.symm
    exact eq_neg_of_add_eq_zero_left this
  have hsix : a ^ 6 = 1 := by
    calc
      a ^ 6 = (a ^ 3) ^ 2 := by ring
      _ = (-1 : ZMod q) ^ 2 := by rw [hcube]
      _ = 1 := by ring
  have ha0 : a ≠ 0 := by
    intro h0
    have : (1 : ZMod q) = 0 := by simpa [h0] using hpoly
    exact one_ne_zero this
  have hneg1 : (-1 : ZMod q) ≠ 1 := by
    intro h
    have h2z : (2 : ZMod q) = 0 := by
      have hsub : (1 : ZMod q) - -1 = 2 := by ring
      have hzero : (1 : ZMod q) - -1 = 0 := by rw [h]; ring
      exact hsub.symm.trans hzero
    have hd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).1 (by simpa using h2z)
    exact hq_ne2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 hd)
  have hdiv : orderOf a ∣ 6 := orderOf_dvd_of_pow_eq_one hsix
  have hle : orderOf a ≤ 6 := Nat.le_of_dvd (by decide) hdiv
  have hpos : 0 < orderOf a := Nat.pos_of_dvd_of_pos hdiv (by decide)
  have hord : orderOf a = 6 := by
    interval_cases hor : orderOf a
    · exfalso
      have ha1 : a = 1 := (orderOf_eq_one_iff).1 hor
      have : (1 : ZMod q) = 0 := by simpa [ha1] using hpoly
      exact one_ne_zero this
    · exfalso
      have ha2 : a ^ 2 = 1 := (orderOf_dvd_iff_pow_eq_one).1 (by simp [hor])
      have : a = -1 := by
        have : a ^ 3 = a := by rw [pow_succ, ha2, one_mul]
        exact this.symm.trans hcube
      exact ha_ne_neg this
    · exfalso
      have ha3 : a ^ 3 = 1 := (orderOf_dvd_iff_pow_eq_one).1 (by simp [hor])
      exact hneg1 (hcube.symm.trans ha3)
    · exfalso
      have : (4 : ℕ) ∣ 6 := by simpa [hor] using hdiv
      norm_num at this
    · exfalso
      have : (5 : ℕ) ∣ 6 := by simpa [hor] using hdiv
      norm_num at this
    · rfl
  have hfermat : a ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha0
  have h6 : 6 ∣ q - 1 := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hfermat
  obtain ⟨m, hm⟩ := h6
  have hq1 : q = 6 * m + 1 := by
    have hle : 1 ≤ q := Nat.Prime.one_le hq
    calc
      q = q - 1 + 1 := (Nat.sub_add_cancel hle).symm
      _ = 6 * m + 1 := by rw [hm]
  rw [hq1, Nat.mul_add_mod_self_left]
