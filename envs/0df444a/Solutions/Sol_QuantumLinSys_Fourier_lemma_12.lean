-- Prove2me | solution 1 for QuantumLinSys.Fourier.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-14T20:33:07.493043+00:00
-- url     : https://prove2.me/submissions/fc8b03ee-22b5-455a-abef-bb73ae9c2ba4

import Mathlib
import Definitions.Def_QuantumLinSys_Fourier_Setting
import Theorems.Thm_QuantumLinSys_Fourier_eq_27

theorem solution :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ κ ε : ℝ,
      1 ≤ κ → 0 < ε → ε < 1 / 2 →
        ∃ yJ zK : ℝ,
          c * (κ * Real.sqrt (Real.log (κ / ε))) ≤ yJ ∧
          yJ ≤ C * (κ * Real.sqrt (Real.log (κ / ε))) ∧
          c * Real.sqrt (Real.log (κ / ε)) ≤ zK ∧
          zK ≤ C * Real.sqrt (Real.log (κ / ε)) ∧
          ∀ x ∈ QuantumLinSys.Chebyshev.Dκ κ,
            ‖QuantumLinSys.Fourier.gTrunc yJ zK x - ((1 / x : ℝ) : ℂ)‖ ≤ ε := by
  refine ⟨Real.sqrt 8, Real.sqrt 8, Real.sqrt_pos.mpr (by norm_num),
    Real.sqrt_pos.mpr (by norm_num), ?_⟩
  intro κ ε hκ hε hε_half
  have hκ_pos : 0 < κ := by linarith
  have hκε_gt_one : 1 < κ / ε := by
    rw [one_lt_div hε]
    linarith
  have hlog_pos : 0 < Real.log (κ / ε) := Real.log_pos hκε_gt_one
  have hlog_nonneg : 0 ≤ Real.log (κ / ε) := hlog_pos.le
  set L : ℝ := Real.sqrt (Real.log (κ / ε))
  set yJ : ℝ := Real.sqrt 8 * (κ * L)
  set zK : ℝ := Real.sqrt 8 * L
  refine ⟨yJ, zK, le_rfl, le_rfl, le_rfl, le_rfl, ?_⟩
  intro x hx
  have hyJ : 0 ≤ yJ := by positivity
  have hzK : 0 ≤ zK := by positivity
  have hx_abs : 1 / κ ≤ |x| := by
    rcases hx with hx_neg | hx_pos
    · have hx1 : x ≤ -1 / κ := hx_neg.2
      have hneg : -1 / κ < 0 := by rw [neg_div]; exact neg_lt_zero.mpr (div_pos one_pos hκ_pos)
      have hx0 : x < 0 := lt_of_le_of_lt hx1 hneg
      rw [abs_of_neg hx0]
      linarith [show (-1 : ℝ) / κ = -(1 / κ) by ring]
    · have hx1 : 1 / κ ≤ x := hx_pos.1
      have hx0 : 0 < x := lt_of_lt_of_le (div_pos one_pos hκ_pos) hx1
      rw [abs_of_pos hx0]
      exact hx1
  have hx_abs_pos : 0 < |x| := lt_of_lt_of_le (div_pos one_pos hκ_pos) hx_abs
  have hx_ne : x ≠ 0 := abs_pos.mp hx_abs_pos
  have heq27 := QuantumLinSys.Fourier.eq_27 x yJ zK hx_ne hyJ hzK
  have hzK_sq : zK ^ 2 / 2 = 4 * Real.log (κ / ε) := by
    dsimp [zK, L]
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hlog_nonneg]
    ring
  have h_exp_zK : Real.exp (-zK ^ 2 / 2) = (ε / κ) ^ 4 := by
    have hneg : -zK ^ 2 / 2 = (4 : ℕ) * (-Real.log (κ / ε)) := by
      have : zK ^ 2 / 2 = 4 * Real.log (κ / ε) := hzK_sq
      linarith
    rw [hneg, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (div_pos hκ_pos hε), inv_div]
  have hκx : 1 ≤ κ * |x| := by
    have h1 := mul_le_mul_of_nonneg_left hx_abs hκ_pos.le
    rwa [mul_one_div_cancel hκ_pos.ne'] at h1
  have hxyJ_sq : zK ^ 2 / 2 ≤ (x * yJ) ^ 2 / 2 := by
    have h1 : (x * yJ) ^ 2 / 2 = (κ * |x|) ^ 2 * (zK ^ 2 / 2) := by
      dsimp [yJ, zK, L]
      rw [mul_pow, mul_pow, mul_pow, ← sq_abs x]
      ring
    rw [h1]
    have hzK2_nonneg : 0 ≤ zK ^ 2 / 2 := by positivity
    have hsq : 1 ≤ (κ * |x|) ^ 2 := by nlinarith
    calc zK ^ 2 / 2 = 1 * (zK ^ 2 / 2) := by ring
      _ ≤ (κ * |x|) ^ 2 * (zK ^ 2 / 2) := mul_le_mul_of_nonneg_right hsq hzK2_nonneg
  have h_exp_xyJ : Real.exp (-(x * yJ) ^ 2 / 2) ≤ (ε / κ) ^ 4 := by
    rw [← h_exp_zK]
    exact Real.exp_le_exp.mpr (by linarith)
  have hinv_abs : (|x|)⁻¹ ≤ κ := by
    have h := (one_div_le hκ_pos hx_abs_pos).mp hx_abs
    simpa [one_div] using h
  have h_bound_1 : Real.exp (-(x * yJ) ^ 2 / 2) / |x| ≤ κ * (ε / κ) ^ 4 := by
    rw [div_eq_mul_inv]
    calc Real.exp (-(x * yJ) ^ 2 / 2) * |x|⁻¹
        ≤ (ε / κ) ^ 4 * κ := mul_le_mul h_exp_xyJ hinv_abs (by positivity) (by positivity)
      _ = κ * (ε / κ) ^ 4 := by ring
  have h_bound_2 : 2 * Real.exp (-zK ^ 2 / 2) / |x| ≤ 2 * (κ * (ε / κ) ^ 4) := by
    rw [h_exp_zK, div_eq_mul_inv, mul_assoc]
    have h1 : (ε / κ) ^ 4 * |x|⁻¹ ≤ (ε / κ) ^ 4 * κ :=
      mul_le_mul_of_nonneg_left hinv_abs (by positivity)
    linarith
  have h_ratio : ε / κ ≤ 1 / 2 := by
    have : ε / κ ≤ ε / 1 := div_le_div_of_nonneg_left hε.le zero_lt_one hκ
    linarith
  have h_pow3 : (ε / κ) ^ 3 ≤ (1 / 2 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) h_ratio 3
  have h_final : 3 * (κ * (ε / κ) ^ 4) ≤ ε := by
    have h_eq : 3 * (κ * (ε / κ) ^ 4) = 3 * ε * (ε / κ) ^ 3 := by
      field_simp [hκ_pos.ne']
    rw [h_eq]
    calc 3 * ε * (ε / κ) ^ 3
        ≤ 3 * ε * (1 / 2 : ℝ) ^ 3 := mul_le_mul_of_nonneg_left h_pow3 (by positivity)
      _ ≤ ε := by linarith
  linarith
