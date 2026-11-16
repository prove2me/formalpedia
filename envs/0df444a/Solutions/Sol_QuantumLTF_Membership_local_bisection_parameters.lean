-- Prove2me | solution 1 for QuantumLTF.Membership.local_bisection_parameters
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T19:16:45.858539+00:00
-- url     : https://prove2.me/submissions/54d0f960-e8a1-4247-8dd4-df7c17e03084

import Mathlib

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η < 1 / 8 →
      ∃ q : ℕ, ((q : ℕ) : ℝ) ≤ C * Real.log (1 / η) ∧
        1 / (2 : ℝ) ^ (q + 2) ≤ η := by
  refine ⟨3, by norm_num, ?_⟩
  intro η hη hη'
  let y : ℝ := 1 / η
  let r : ℝ := Real.logb 2 y
  let q : ℕ := ⌈r⌉₊
  have hy8 : 8 < y := by
    dsimp [y]
    exact (lt_div_iff₀ hη).2 (by nlinarith)
  have hy : 0 < y := lt_trans (by norm_num) hy8
  have hlog2 : (0 : ℝ) < Real.log 2 := by
    exact lt_trans (by norm_num : (0 : ℝ) < 0.6931471803) Real.log_two_gt_d9
  have hlog2half : (1 / 2 : ℝ) < Real.log 2 := by
    exact lt_trans (by norm_num : (1 / 2 : ℝ) < 0.6931471803) Real.log_two_gt_d9
  have hr : 0 ≤ r :=
    Real.logb_nonneg (by norm_num) (le_of_lt (lt_trans (by norm_num : (1 : ℝ) < 8) hy8))
  have hrq : r ≤ (q : ℝ) := Nat.le_ceil _
  have hqr : (q : ℝ) < r + 1 := Nat.ceil_lt_add_one hr
  have hlogy : Real.log y = Real.log (1 / η) := by rfl
  have hrform : r = Real.log y / Real.log 2 := by rfl
  have hlogybig : 1 < Real.log y := by
    have hlog8 : Real.log 8 < Real.log y :=
      Real.strictMonoOn_log (by norm_num : (8 : ℝ) ∈ Set.Ioi 0) hy hy8
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at hlog8
    have hthree : (3 : ℝ) * Real.log 2 < Real.log y := by
      norm_num at hlog8 ⊢
      exact hlog8
    linarith [hlog2half, hthree]
  have hqbound : (q : ℝ) ≤ 3 * Real.log (1 / η) := by
    rw [← hlogy]
    rw [hrform] at hqr
    have hrlt : r < 2 * Real.log y := by
      rw [hrform]
      exact (div_lt_iff₀ hlog2).2 (by nlinarith)
    linarith
  have hypowR : y ≤ (2 : ℝ) ^ (q : ℝ) :=
    (Real.logb_le_iff_le_rpow (b := 2) (x := y) (y := (q : ℝ)) (by norm_num) hy).1 hrq
  have hypow : y ≤ (2 : ℝ) ^ q := by simpa [Real.rpow_natCast] using hypowR
  have hinv : ((2 : ℝ) ^ q)⁻¹ ≤ y⁻¹ :=
    (inv_le_inv₀ (pow_pos (by norm_num) q) hy).2 hypow
  have hyinv : y⁻¹ = η := by
    dsimp [y]
    field_simp
  refine ⟨q, hqbound, ?_⟩
  rw [show q + 2 = q + 2 by rfl, pow_add]
  norm_num
  rw [div_eq_mul_inv, mul_assoc]
  have : 1 / (2 : ℝ) ^ q ≤ η := by
    rw [div_eq_mul_inv, one_mul, ← hyinv]
    exact hinv
  nlinarith
