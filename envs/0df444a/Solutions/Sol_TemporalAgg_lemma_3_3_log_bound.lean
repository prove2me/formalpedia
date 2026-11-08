-- Prove2me | solution 1 for TemporalAgg.lemma_3_3_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T15:25:01.483046+00:00
-- url     : https://prove2.me/submissions/e5b5c028-571e-45c1-905c-f68799c5b4ad

import Mathlib

/-- The logarithmic estimate in the proof of Lemma 3.3 (temporal aggregation). -/
theorem solution (k : ℕ) (hk : 2 ≤ k) :
    -Real.logb (3 / 2) ((k : ℝ) / ((k : ℝ) - 1)) ≥
        -(1 / Real.log (3 / 2)) * (1 / ((k : ℝ) - 1)) ∧
      -(1 / Real.log (3 / 2)) * (1 / ((k : ℝ) - 1)) ≥ -5 / (k : ℝ) ∧
      Real.log ((k : ℝ) / ((k : ℝ) - 1)) ≤ 1 / ((k : ℝ) - 1) ∧
      1 / ((k : ℝ) - 1) ≤ 2 / (k : ℝ) ∧
      1 / Real.log (3 / 2) < 2.5 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkm1 : 0 < (k : ℝ) - 1 := by linarith
  have hk1 : 0 < (k : ℝ) := hk0
  have hq : 0 < (k : ℝ) / ((k : ℝ) - 1) := div_pos hk0 hkm1
  have hlog32 : 0.4 < Real.log (3 / 2) := by
    have h3 := Real.log_three_gt_d9
    have h2 := Real.log_two_lt_d9
    have hd : Real.log (3 / 2) = Real.log 3 - Real.log 2 :=
      Real.log_div (by norm_num) (by norm_num)
    linarith
  have hlog32pos : 0 < Real.log (3 / 2) := by linarith
  have hlogq : Real.log ((k : ℝ) / ((k : ℝ) - 1)) ≤ 1 / ((k : ℝ) - 1) := by
    have h := Real.log_le_sub_one_of_pos hq
    have hsub : (k : ℝ) / ((k : ℝ) - 1) - 1 = 1 / ((k : ℝ) - 1) := by
      field_simp
      ring
    linarith
  constructor
  · rw [Real.logb, div_eq_mul_inv]
    have h : Real.log ((k : ℝ) / ((k : ℝ) - 1)) * (Real.log (3 / 2))⁻¹ ≤
        (1 / ((k : ℝ) - 1)) * (Real.log (3 / 2))⁻¹ :=
      mul_le_mul_of_nonneg_right hlogq (le_of_lt (inv_pos.mpr hlog32pos))
    have heq : (1 / ((k : ℝ) - 1)) * (Real.log (3 / 2))⁻¹ =
        1 / Real.log (3 / 2) * (1 / ((k : ℝ) - 1)) := by
      field_simp
    rw [heq] at h
    simpa [neg_mul] using neg_le_neg h
  constructor
  · have h4 : 1 / ((k : ℝ) - 1) ≤ 2 / (k : ℝ) := by
      rw [div_le_div_iff₀ hkm1 hk0]
      nlinarith
    have h5 : 1 / Real.log (3 / 2) < 2.5 := by
      rw [div_lt_iff₀ hlog32pos]
      nlinarith
    have hpos : 0 < 1 / ((k : ℝ) - 1) := div_pos one_pos hkm1
    have hprod : (1 / Real.log (3 / 2)) * (1 / ((k : ℝ) - 1)) < 2.5 * (2 / (k : ℝ)) := by
      apply mul_lt_mul h5 h4 hpos (by norm_num : (0:ℝ) ≤ 2.5)
    have hright : 2.5 * (2 / (k : ℝ)) = 5 / (k : ℝ) := by
      field_simp
      ring
    rw [hright] at hprod
    have hneg := neg_lt_neg hprod
    rw [neg_mul, neg_div]
    exact le_of_lt hneg
  constructor
  · exact hlogq
  constructor
  · rw [div_le_div_iff₀ hkm1 hk0]
    nlinarith
  · rw [div_lt_iff₀ hlog32pos]
    nlinarith
