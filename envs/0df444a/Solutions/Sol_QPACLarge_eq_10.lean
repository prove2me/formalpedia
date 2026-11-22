-- Prove2me | solution 1 for QPACLarge.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T13:21:16.037795+00:00
-- url     : https://prove2.me/submissions/30b57ebc-7db0-4d32-8cd8-f8a3d4712dea

import Mathlib

open Filter

set_option autoImplicit false

theorem solution (lam : ℕ → ℝ) (s : ℕ → ℕ) (hpos : ∀ n, 0 < lam n)
    (h9 : ∀ᶠ n : ℕ in atTop, ((2 : ℝ) ^ s n)⁻¹ ≤ lam n ∧ lam n ≤ 4 * ((2 : ℝ) ^ s n)⁻¹)
    (hlow : ∀ c : ℕ, ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ c * (2 : ℝ) ^ (-(n : ℝ) / 2) ≤ lam n)
    (hup : ∀ c : ℕ, ∀ᶠ n : ℕ in atTop, lam n ≤ (n : ℝ) ^ (-(c : ℝ))) :
    (∀ c : ℕ, ∀ᶠ n : ℕ in atTop, (c : ℝ) * Real.log n ≤ s n) ∧
      (∀ c : ℕ, ∀ᶠ n : ℕ in atTop, (c : ℝ) * Real.log n ≤ (n : ℝ) / 2 - s n) := by
  constructor
  · intro c
    filter_upwards [h9, hup c, eventually_ge_atTop (1 : ℕ)] with n h9n hupn hn1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
    have hPpos : 0 < (2 : ℝ) ^ s n := pow_pos (by norm_num) _
    have hlampos : 0 < lam n := hpos n
    -- 1/lam ≤ 2^{s n}
    have hP_ge : (lam n)⁻¹ ≤ (2 : ℝ) ^ s n := by
      rw [inv_eq_one_div, div_le_iff₀ hlampos]
      have h := h9n.1
      rw [inv_eq_one_div, div_le_iff₀ hPpos] at h
      calc (1 : ℝ) ≤ lam n * (2 : ℝ) ^ s n := h
        _ = (2 : ℝ) ^ s n * lam n := by ring
    -- n^c ≤ 1/lam
    have hnc : (n : ℝ) ^ c ≤ (lam n)⁻¹ := by
      have h := (inv_le_inv₀ (Real.rpow_pos_of_pos hnpos _) hlampos).mpr hupn
      rwa [Real.rpow_neg hnpos.le, inv_inv, Real.rpow_natCast] at h
    have hnc_le_P : (n : ℝ) ^ c ≤ (2 : ℝ) ^ s n := hnc.trans hP_ge
    -- s n = logb 2 (2^{s n}) ≥ logb 2 (n^c) = c logb 2 n
    have hsn_ge : (c : ℝ) * Real.logb 2 (n : ℝ) ≤ (s n : ℝ) := by
      have hlogP : (s n : ℝ) = Real.logb 2 ((2 : ℝ) ^ s n) := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
        ring
      rw [hlogP]
      have hmono : Real.logb 2 ((n : ℝ) ^ c) ≤ Real.logb 2 ((2 : ℝ) ^ s n) :=
        (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (pow_pos hnpos c) hPpos).mpr hnc_le_P
      rwa [Real.logb_pow] at hmono
    -- log n ≤ logb 2 n
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2le : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    have hlogb_ge : Real.log (n : ℝ) ≤ Real.logb 2 (n : ℝ) := by
      change Real.log (n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2
      rw [le_div_iff₀ hlog2pos]
      nlinarith
    have hclog : (c : ℝ) * Real.log (n : ℝ) ≤ (c : ℝ) * Real.logb 2 (n : ℝ) :=
      mul_le_mul_of_nonneg_left hlogb_ge (by positivity)
    linarith
  · intro c
    filter_upwards [h9, hlow (c + 3), eventually_ge_atTop (2 : ℕ)] with n h9n hlown hn2
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn2)
    have hPpos : 0 < (2 : ℝ) ^ s n := pow_pos (by norm_num) _
    have hlampos : 0 < lam n := hpos n
    -- 2^{s n} ≤ 4/lam
    have hP_le : (2 : ℝ) ^ s n ≤ 4 / lam n := by
      rw [le_div_iff₀ hlampos]
      have h := h9n.2
      rw [inv_eq_one_div, mul_one_div, le_div_iff₀ hPpos] at h
      rwa [mul_comm] at h
    -- 4/lam ≤ 4 * 2^{n/2} / n^{c+3}
    have hlowpos : 0 < (n : ℝ) ^ (c + 3) * (2 : ℝ) ^ (-(n : ℝ) / 2) :=
      mul_pos (pow_pos hnpos _) (Real.rpow_pos_of_pos (by norm_num) _)
    have hbase_le : 4 / lam n ≤ 4 * (2 : ℝ) ^ ((n : ℝ) / 2) / (n : ℝ) ^ (c + 3) := by
      calc 4 / lam n = 4 * (1 / lam n) := by ring
        _ ≤ 4 * (1 / ((n : ℝ) ^ (c + 3) * (2 : ℝ) ^ (-(n : ℝ) / 2))) :=
            mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hlowpos hlown) (by norm_num)
        _ = 4 * (2 : ℝ) ^ ((n : ℝ) / 2) / (n : ℝ) ^ (c + 3) := by
            rw [show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring,
              Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
            field_simp
    have hP_bound : (2 : ℝ) ^ s n ≤ 4 * (2 : ℝ) ^ ((n : ℝ) / 2) / (n : ℝ) ^ (c + 3) :=
      hP_le.trans hbase_le
    have hRpos : 0 < 4 * (2 : ℝ) ^ ((n : ℝ) / 2) / (n : ℝ) ^ (c + 3) := by positivity
    -- take logb 2
    have hsn_le : (s n : ℝ) ≤ 2 + (n : ℝ) / 2 - ((c : ℝ) + 3) * Real.logb 2 (n : ℝ) := by
      have hlogP : (s n : ℝ) = Real.logb 2 ((2 : ℝ) ^ s n) := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
        ring
      rw [hlogP]
      have hmono : Real.logb 2 ((2 : ℝ) ^ s n) ≤
          Real.logb 2 (4 * (2 : ℝ) ^ ((n : ℝ) / 2) / (n : ℝ) ^ (c + 3)) :=
        (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hPpos hRpos).mpr hP_bound
      have hcomp : Real.logb 2 (4 * (2 : ℝ) ^ ((n : ℝ) / 2) / (n : ℝ) ^ (c + 3)) =
          2 + (n : ℝ) / 2 - ((c : ℝ) + 3) * Real.logb 2 (n : ℝ) := by
        rw [Real.logb_div (by positivity) (by positivity),
          Real.logb_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity)]
        have h4 : Real.logb 2 (4 : ℝ) = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow,
            Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
          norm_num
        have h2n : Real.logb 2 ((2 : ℝ) ^ ((n : ℝ) / 2)) = (n : ℝ) / 2 :=
          Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
        have hnpow : Real.logb 2 ((n : ℝ) ^ (c + 3)) = ((c : ℝ) + 3) * Real.logb 2 (n : ℝ) := by
          rw [Real.logb_pow]
          push_cast
          ring
        rw [h4, h2n, hnpow]
      rwa [hcomp] at hmono
    -- logb 2 n ≥ 1
    have hlogb_ge1 : 1 ≤ Real.logb 2 (n : ℝ) := by
      have h := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
        (by norm_num : 0 < (2 : ℝ)) hnpos).mpr (by exact_mod_cast hn2)
      rwa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h
    -- log n ≤ logb 2 n
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2le : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hn2))
    have hlogb_ge : Real.log (n : ℝ) ≤ Real.logb 2 (n : ℝ) := by
      change Real.log (n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2
      rw [le_div_iff₀ hlog2pos]
      nlinarith
    have hclog : (c : ℝ) * Real.log (n : ℝ) ≤ (c : ℝ) * Real.logb 2 (n : ℝ) :=
      mul_le_mul_of_nonneg_left hlogb_ge (by positivity)
    have hfin : 2 + (n : ℝ) / 2 - ((c : ℝ) + 3) * Real.logb 2 (n : ℝ) ≤
        (n : ℝ) / 2 - (c : ℝ) * Real.log (n : ℝ) := by
      nlinarith
    linarith

