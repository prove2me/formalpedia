-- Prove2me | solution 1 for RevRedSAT.lemma_B_7
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T16:34:51.464264+00:00
-- url     : https://prove2.me/submissions/a9b499fe-2984-4dfe-b0d3-ff77d769fb37

import Mathlib
import Definitions.Def_RevRedSAT_mu

set_option autoImplicit false

open RevRedSAT in
theorem solution (d j s p : ℕ) (hd : 2 ≤ d) (hj : 2 ≤ j) (hp : 1 ≤ p) (hps : p < s)
    (hs : s ≤ d) :
    (2 : ℝ) ^ (-(deltaOf j * (ws d j (s - p) / 2))) +
      (2 : ℝ) ^ (-(deltaOf j * (ws d j p * tp d j p / 2))) ≤ 1 := by
  set c := s - p with hc
  have hc1 : 1 ≤ c := by omega
  have hcd : c + 1 ≤ d := by omega
  set N : ℕ := 2 ^ (j + 1) * d with hN
  have h8 : 8 ≤ 2 ^ (j + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN16 : 16 ≤ N := by
    have := Nat.mul_le_mul h8 hd
    omega
  have h2j : 2 ^ j ≤ N := by
    have : 2 ^ j ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ^ j ≤ 2 ^ (j + 1) := this
      _ ≤ 2 ^ (j + 1) * d := Nat.le_mul_of_pos_right _ (by omega)
  have h4d : 4 * d ≤ N := by
    have := Nat.mul_le_mul_right d h8
    omega
  -- the natural-number core inequality
  have key : 32 * 2 ^ j * N ^ (4 * c - 4) ≤ 2 ^ (N * N) := by
    calc 32 * 2 ^ j * N ^ (4 * c - 4) ≤ (N * N) * N * N ^ (4 * c - 4) := by
          gcongr
          nlinarith
      _ = N ^ (4 * c - 1) := by
          rw [show 4 * c - 1 = (4 * c - 4) + 3 by omega]
          ring
      _ ≤ N ^ N := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ (2 ^ N) ^ N := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le N
      _ = 2 ^ (N * N) := by rw [← pow_mul]
  have keyR : (32 : ℝ) * 2 ^ j * (N : ℝ) ^ (4 * c - 4) ≤ (2 : ℝ) ^ (N * N) := by
    exact_mod_cast key
  have hNr : (N : ℝ) = 2 * 2 ^ j * d := by
    simp only [hN]; push_cast; ring
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha : Aval d j = N := by
    unfold Aval deltaOf
    rw [hNr, div_inv_eq_mul]
    ring
  have hws : ∀ m : ℕ, 1 ≤ m → ws d j m = (1 / 2) / (N : ℝ) ^ (4 * m - 4) := by
    intro m hm
    unfold ws
    rw [ha]
    have : ((4 : ℤ) - 4 * (m : ℤ)) = -(((4 * m - 4 : ℕ)) : ℤ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this, zpow_neg, zpow_natCast]
    ring
  have htp : tp d j p = (N : ℝ) ^ (4 * p) / (4 * d) := by
    unfold tp; rw [ha]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have h2jpos : (0 : ℝ) < 2 ^ j := by positivity
  set x := deltaOf j * (ws d j c / 2) with hxdef
  set y := deltaOf j * (ws d j p * tp d j p / 2) with hydef
  have hx : x = 1 / (4 * 2 ^ j * (N : ℝ) ^ (4 * c - 4)) := by
    rw [hxdef, hws c hc1]
    unfold deltaOf
    field_simp
    ring
  have hy : y = (N : ℝ) ^ 3 / 8 := by
    rw [hydef, hws p hp, htp]
    unfold deltaOf
    have hpow : (N : ℝ) ^ (4 * p) = (N : ℝ) ^ (4 * p - 4) * (N : ℝ) ^ 4 := by
      rw [← pow_add]; congr 1; omega
    rw [hpow]
    have hNne : (N : ℝ) ^ (4 * p - 4) ≠ 0 := by positivity
    field_simp
    rw [hNr]
    ring
  have hNpowpos : (0 : ℝ) < (N : ℝ) ^ (4 * c - 4) := by positivity
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx2 : x ≤ 2 := by
    rw [hx, div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ (N : ℝ) ^ (4 * c - 4) :=
      one_le_pow₀ (by exact_mod_cast (show 1 ≤ N by omega))
    nlinarith [mul_le_mul h1 h2 zero_le_one (by positivity)]
  -- bound on the first term
  have e1 : (2 : ℝ) ^ (-x) ≤ 1 / (1 + x / 2) := by
    have hge : 1 + x / 2 ≤ (2 : ℝ) ^ x := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      have := Real.add_one_le_exp (Real.log 2 * x)
      have hl := Real.log_two_gt_d9
      nlinarith
    rw [Real.rpow_neg (by norm_num), ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hge
  -- bound on the second term
  have e2 : (2 : ℝ) ^ (-y) ≤ ((2 : ℝ) ^ (N * N))⁻¹ := by
    have hNy : ((N * N : ℕ) : ℝ) ≤ y := by
      rw [hy]; push_cast
      have : (16 : ℝ) ≤ N := by exact_mod_cast hN16
      nlinarith [mul_pos hNpos hNpos]
    calc (2 : ℝ) ^ (-y) ≤ (2 : ℝ) ^ (-((N * N : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hNy)
      _ = ((2 : ℝ) ^ (N * N))⁻¹ := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  have e3 : ((2 : ℝ) ^ (N * N))⁻¹ ≤ x / 4 := by
    rw [hx]
    rw [← one_div, div_div, one_div_le_one_div (by positivity) (by positivity)]
    nlinarith
  have hfin : 1 / (1 + x / 2) + x / 4 ≤ 1 := by
    rw [div_add_div _ _ (by positivity) (by norm_num), div_le_one (by positivity)]
    nlinarith
  linarith
