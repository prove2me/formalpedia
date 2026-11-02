-- Prove2me | solution 1 for QuantumMaxCutEnergy.rank3_series_negative_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T19:12:04.005229+00:00
-- url     : https://prove2.me/submissions/1f58ac05-cf40-4f8a-8994-fab081a0f592

import Mathlib
open scoped BigOperators

/-- The negative half of the rank-3 odd-series ratio bound: for `t ∈ [-1,0]` the two-term
majorant `c 0 * t + c 1 * t^3` already suffices, so no normalisation `∑ c = 1` is needed. -/
theorem solution (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hsum : Summable c)
    (hc0 : 8 / (3 * Real.pi) ≤ c 0) (hc1 : 4 / (15 * Real.pi) ≤ c 1)
    {t : ℝ} (ht1 : -1 ≤ t) (ht0 : t ≤ 0) :
    (∑' k, c k * t ^ (2 * k + 1)) ≤ (0.046 : ℝ) + 0.954 * t := by
  classical
  -- summability of the odd series at |t| ≤ 1
  have hsumm : Summable (fun k : ℕ => c k * t ^ (2 * k + 1)) := by
    refine hsum.of_norm_bounded (g := c) (fun k => ?_)
    have htabs : |t| ≤ 1 := abs_le.mpr ⟨ht1, by linarith⟩
    have h1 : |t ^ (2 * k + 1)| = |t| ^ (2 * k + 1) := abs_pow t _
    have h2 : |t| ^ (2 * k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg t) htabs
    calc ‖c k * t ^ (2 * k + 1)‖ = |c k * t ^ (2 * k + 1)| := Real.norm_eq_abs _
      _ = |c k| * |t ^ (2 * k + 1)| := abs_mul _ _
      _ = c k * |t| ^ (2 * k + 1) := by rw [abs_of_nonneg (hc k), h1]
      _ ≤ c k * 1 := by
        have := h2
        nlinarith [hc k]
      _ = c k := mul_one _
  -- split off the first two terms
  have hsplit := hsumm.sum_add_tsum_nat_add 2
  have htail : (∑' k : ℕ, c (k + 2) * t ^ (2 * (k + 2) + 1)) ≤ 0 := by
    refine tsum_nonpos (fun k => ?_)
    have hodd : Odd (2 * (k + 2) + 1) := ⟨k + 2, by ring⟩
    have hneg : t ^ (2 * (k + 2) + 1) ≤ 0 := hodd.pow_nonpos ht0
    have := hc (k + 2)
    nlinarith
  have hbsum : (∑' k : ℕ, c k * t ^ (2 * k + 1)) ≤ c 0 * t + c 1 * t ^ 3 := by
    have h2 : ∑ i ∈ Finset.range 2, c i * t ^ (2 * i + 1) = c 0 * t + c 1 * t ^ 3 := by
      norm_num [Finset.sum_range_succ]
    linarith [hsplit, htail, h2]
  -- the two coefficients against the linear-plus-cubic majorant
  have h0 : c 0 * t ≤ (8 / (3 * Real.pi)) * t := by
    have hnn : 0 ≤ c 0 - 8 / (3 * Real.pi) := by linarith
    nlinarith [mul_nonneg hnn (show (0:ℝ) ≤ -t by linarith)]
  have h1 : c 1 * t ^ 3 ≤ (4 / (15 * Real.pi)) * t ^ 3 := by
    have hnn : 0 ≤ c 1 - 4 / (15 * Real.pi) := by linarith
    have ht3 : t ^ 3 ≤ 0 := (show Odd 3 by decide).pow_nonpos ht0
    nlinarith [mul_nonneg hnn (show (0:ℝ) ≤ -t ^ 3 by linarith)]
  -- the explicit majorant is below the affine bound on [-1,0]
  have hpoly : (8 / (3 * Real.pi)) * t + (4 / (15 * Real.pi)) * t ^ 3 ≤ 0.046 + 0.954 * t := by
    have hpil : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
    have hpih : Real.pi < 3.141593 := Real.pi_lt_d6
    have hpip : (0:ℝ) < Real.pi := Real.pi_pos
    -- clear the denominators: multiply by 45 π
    have hden : (0:ℝ) < 45 * Real.pi := by positivity
    have heq : (8 / (3 * Real.pi)) * t + (4 / (15 * Real.pi)) * t ^ 3
        = (120 * t + 12 * t ^ 3) / (45 * Real.pi) := by
      field_simp
      ring
    rw [heq, div_le_iff₀ hden]
    -- certificate for the cubic
    have hcert : (0:ℝ) ≤ 12 * (t + 0.6427) ^ 2 * (-t + 1.2854) := by
      have : (0:ℝ) ≤ -t + 1.2854 := by linarith
      have hsq : (0:ℝ) ≤ (t + 0.6427) ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg hsq this]
    nlinarith [hcert, hpil, hpih]
  linarith [hbsum, h0, h1, hpoly]
