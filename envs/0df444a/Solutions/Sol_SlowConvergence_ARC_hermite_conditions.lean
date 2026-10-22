-- Prove2me | solution 1 for SlowConvergence.ARC.hermite_conditions
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:19:13.011645+00:00
-- url     : https://prove2.me/submissions/cab78433-0fe6-45dd-8028-64758f48ca33

import Mathlib
import Definitions.Def_SlowConvergence_ARC_Data
import Definitions.Def_SlowConvergence_ARC_Pieces

set_option autoImplicit false
open SlowConvergence.ARC

lemma S_eta_pos {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) : 0 < eta τ := by
  unfold eta
  have h3 : 0 < 3 - 2 * τ := by linarith
  have : 2 / 3 < 2 / (3 - 2 * τ) := div_lt_div_of_pos_left (by norm_num) h3 (by linarith)
  linarith

lemma S_sk_pos (τ : ℝ) (k : ℕ) : 0 < sk τ k := by
  unfold sk
  exact Real.rpow_pos_of_pos (by positivity) _

lemma S_base_le_one (k : ℕ) : 1 / ((k : ℝ) + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

lemma S_sk_le_one {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) (k : ℕ) : sk τ k ≤ 1 := by
  unfold sk
  have := S_eta_pos h0 h1
  exact Real.rpow_le_one (by positivity) (S_base_le_one k) (by linarith)

lemma S_sk_sq (τ : ℝ) (k : ℕ) : sk τ k ^ 2 = (1 / ((k : ℝ) + 1)) ^ (2 / 3 + 2 * eta τ) := by
  unfold sk
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

lemma S_sk_cube (τ : ℝ) (k : ℕ) : sk τ k ^ 3 = (1 / ((k : ℝ) + 1)) ^ (1 + 3 * eta τ) := by
  unfold sk
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

lemma S_poly_d1 (c0 c1 c2 c3 c4 c5 t : ℝ) :
    HasDerivAt (fun t => c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4 + c5 * t ^ 5)
      (c1 + 2 * c2 * t + 3 * c3 * t ^ 2 + 4 * c4 * t ^ 3 + 5 * c5 * t ^ 4) t := by
  have h := (((((hasDerivAt_const t c0).add ((hasDerivAt_id t).const_mul c1)).add
    ((hasDerivAt_pow 2 t).const_mul c2)).add ((hasDerivAt_pow 3 t).const_mul c3)).add
    ((hasDerivAt_pow 4 t).const_mul c4)).add ((hasDerivAt_pow 5 t).const_mul c5)
  refine h.congr_deriv ?_
  try simp only [id]
  try push_cast
  ring

lemma S_poly_d2 (c1 c2 c3 c4 c5 t : ℝ) :
    HasDerivAt (fun t => c1 + 2 * c2 * t + 3 * c3 * t ^ 2 + 4 * c4 * t ^ 3 + 5 * c5 * t ^ 4)
      (2 * c2 + 6 * c3 * t + 12 * c4 * t ^ 2 + 20 * c5 * t ^ 3) t := by
  have h := ((((hasDerivAt_const t c1).add ((hasDerivAt_id t).const_mul (2 * c2))).add
    ((hasDerivAt_pow 2 t).const_mul (3 * c3))).add ((hasDerivAt_pow 3 t).const_mul (4 * c4))).add
    ((hasDerivAt_pow 4 t).const_mul (5 * c5))
  refine h.congr_deriv ?_
  try simp only [id]
  try push_cast
  ring

theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    p τ k 0 = 2 / 3 * (1 / ((k : ℝ) + 1)) ^ (1 + 3 * eta τ) ∧
      p τ k (sk τ k) = 0 ∧
      deriv (p τ k) 0 = -(1 / ((k : ℝ) + 1)) ^ (2 / 3 + 2 * eta τ) ∧
      deriv (p τ k) (sk τ k) = -(1 / ((k : ℝ) + 2)) ^ (2 / 3 + 2 * eta τ) ∧
      iteratedDeriv 2 (p τ k) 0 = 0 ∧
      iteratedDeriv 2 (p τ k) (sk τ k) = 0 := by
  have hs0 := S_sk_pos τ k
  have hsq := S_sk_sq τ k
  have hcube := S_sk_cube τ k
  have hc0 : coeff τ k 0 = 2 / 3 * (sk τ k) ^ 3 := by
    rw [hcube]; rfl
  have hc1 : coeff τ k 1 = -(sk τ k) ^ 2 := by
    rw [hsq]; rfl
  have hc2 : coeff τ k 2 = 0 := rfl
  have hc3 : coeff τ k 3 = 10 / 3 - 4 * phi τ k := rfl
  have hc4 : coeff τ k 4 = (-5 + 7 * phi τ k) / sk τ k := rfl
  have hc5 : coeff τ k 5 = (2 - 3 * phi τ k) / sk τ k ^ 2 := rfl
  have hpfun : p τ k = fun t => coeff τ k 0 + coeff τ k 1 * t + coeff τ k 2 * t ^ 2 +
      coeff τ k 3 * t ^ 3 + coeff τ k 4 * t ^ 4 + coeff τ k 5 * t ^ 5 := rfl
  have hd : ∀ t, HasDerivAt (p τ k) (coeff τ k 1 + 2 * coeff τ k 2 * t + 3 * coeff τ k 3 * t ^ 2 +
      4 * coeff τ k 4 * t ^ 3 + 5 * coeff τ k 5 * t ^ 4) t := by
    intro t
    rw [hpfun]
    exact S_poly_d1 _ _ _ _ _ _ t
  have hdf : deriv (p τ k) = fun t => coeff τ k 1 + 2 * coeff τ k 2 * t + 3 * coeff τ k 3 * t ^ 2 +
      4 * coeff τ k 4 * t ^ 3 + 5 * coeff τ k 5 * t ^ 4 := funext (fun t => (hd t).deriv)
  have hit : ∀ t, iteratedDeriv 2 (p τ k) t = 2 * coeff τ k 2 + 6 * coeff τ k 3 * t +
      12 * coeff τ k 4 * t ^ 2 + 20 * coeff τ k 5 * t ^ 3 := by
    intro t
    rw [iteratedDeriv_succ, iteratedDeriv_one, hdf]
    exact (S_poly_d2 _ _ _ _ _ t).deriv
  have hφ : phi τ k = ((k : ℝ) + 1) ^ mu τ * ((1 / ((k : ℝ) + 1)) ^ mu τ - (1 / ((k : ℝ) + 2)) ^ mu τ) := rfl
  have hmu : mu τ = 2 / 3 + 2 * eta τ := rfl
  have hAB : ((k : ℝ) + 1) ^ mu τ * (1 / ((k : ℝ) + 1)) ^ mu τ = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    rw [mul_one_div_cancel (by positivity), Real.one_rpow]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpfun]; simp only [hc2]; simp [coeff]
  · rw [hpfun]
    simp only [hc0, hc1, hc2, hc3, hc4, hc5]
    field_simp
    ring
  · rw [hdf]; simp only [hc2]; simp [coeff]
  · rw [hdf]
    simp only [hc1, hc2, hc3, hc4, hc5]
    have h4 : (-5 + 7 * phi τ k) / sk τ k * 4 * sk τ k ^ 3 = 4 * (-5 + 7 * phi τ k) * sk τ k ^ 2 := by
      field_simp
    have h5 : (2 - 3 * phi τ k) / sk τ k ^ 2 * 5 * sk τ k ^ 4 = 5 * (2 - 3 * phi τ k) * sk τ k ^ 2 := by
      field_simp
    have hmain : -(sk τ k) ^ 2 + 2 * 0 * sk τ k + 3 * (10 / 3 - 4 * phi τ k) * sk τ k ^ 2 +
        4 * ((-5 + 7 * phi τ k) / sk τ k) * sk τ k ^ 3 + 5 * ((2 - 3 * phi τ k) / sk τ k ^ 2) * sk τ k ^ 4
        = -(sk τ k) ^ 2 + phi τ k * sk τ k ^ 2 := by
      have := h4; have := h5
      nlinarith [h4, h5]
    rw [hmain, hsq, ← hmu, hφ]
    set A := ((k : ℝ) + 1) ^ mu τ
    set B := (1 / ((k : ℝ) + 1)) ^ mu τ
    set C := (1 / ((k : ℝ) + 2)) ^ mu τ
    linear_combination (B - C) * hAB
  · rw [hit]; simp only [hc2]; simp [coeff]
  · rw [hit]
    simp only [hc2, hc3, hc4, hc5]
    field_simp
    ring
