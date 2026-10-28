-- Prove2me | solution 1 for QSPHamSim.Main.rotation_bound
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T02:41:20.08395+00:00
-- url     : https://prove2.me/submissions/02cf4f49-a0f3-4d34-895b-e1cf9c37a14d

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section

theorem solution (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (A₁ B C₁ D : ℝ → ℝ)
    (hunit : ∀ θ : ℝ,
      A₁ θ ^ 2 + B θ ^ 2 + C₁ θ ^ 2 + D θ ^ 2 = 1)
    (hlower : ∀ θ : ℝ,
      ((1 - ε) / (1 + ε)) ^ 2 ≤ A₁ θ ^ 2 + C₁ θ ^ 2)
    (δ : ℝ) (hcos : Real.cos δ = A₁ 0)
    (hsin : Real.sin δ = B 0)
    (hδ : (1 - ε) / (1 + ε) ≤ Real.cos δ) :
    let A₂ := fun θ : ℝ => A₁ θ * Real.cos δ + B θ * Real.sin δ
    ∀ θ : ℝ,
      B θ ^ 2 ≤ 4 * ε / (1 + ε) ^ 2 ∧
      |A₂ θ - A₁ θ| ≤
        2 * ε / (1 + ε) + |B θ| * (2 * Real.sqrt ε / (1 + ε)) ∧
      |A₂ θ - A₁ θ| ≤ 6 * ε := by
  dsimp only
  have hd : 0 < 1 + ε := by positivity
  have hd1 : 1 ≤ 1 + ε := by linarith
  let q := (1 - ε) / (1 + ε)
  let r := 2 * Real.sqrt ε / (1 + ε)
  have hq0 : 0 ≤ q := div_nonneg (by linarith) hd.le
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrat : 1 - q ^ 2 = 4 * ε / (1 + ε) ^ 2 := by
    dsimp [q]
    field_simp
    <;> ring
  have hrsq : r ^ 2 = 4 * ε / (1 + ε) ^ 2 := by
    dsimp [r]
    rw [div_pow, mul_pow, Real.sq_sqrt hε]
    ring
  have hc0 : 0 ≤ Real.cos δ := hq0.trans hδ
  have hcsq : q ^ 2 ≤ Real.cos δ ^ 2 := (sq_le_sq₀ hq0 hc0).2 hδ
  have hsbound : |Real.sin δ| ≤ r := by
    apply abs_le_of_sq_le_sq _ hr0
    rw [hrsq, ← hrat]
    nlinarith [Real.sin_sq_add_cos_sq δ]
  have hcosdist : |Real.cos δ - 1| ≤ 2 * ε / (1 + ε) := by
    rw [abs_of_nonpos (by linarith [Real.cos_le_one δ])]
    have hqeq : 1 - q = 2 * ε / (1 + ε) := by dsimp [q]; field_simp; ring
    linarith
  intro θ
  have hBsq : B θ ^ 2 ≤ 4 * ε / (1 + ε) ^ 2 := by
    rw [← hrat]
    nlinarith [hunit θ, hlower θ, sq_nonneg (D θ)]
  have hB : |B θ| ≤ r := abs_le_of_sq_le_sq (by rw [hrsq]; exact hBsq) hr0
  have hA : |A₁ θ| ≤ 1 := by
    apply (sq_le_one_iff_abs_le_one _).1
    nlinarith [hunit θ, sq_nonneg (B θ), sq_nonneg (C₁ θ), sq_nonneg (D θ)]
  have herr : |A₁ θ * Real.cos δ + B θ * Real.sin δ - A₁ θ| ≤
      2 * ε / (1 + ε) + |B θ| * r := by
    calc
      _ = |A₁ θ * (Real.cos δ - 1) + B θ * Real.sin δ| := by congr 1; ring
      _ ≤ |A₁ θ * (Real.cos δ - 1)| + |B θ * Real.sin δ| := abs_add_le _ _
      _ = |A₁ θ| * |Real.cos δ - 1| + |B θ| * |Real.sin δ| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * (2 * ε / (1 + ε)) + |B θ| * r :=
        add_le_add (mul_le_mul hA hcosdist (abs_nonneg _) (by norm_num))
          (mul_le_mul_of_nonneg_left hsbound (abs_nonneg _))
      _ = _ := by ring
  refine ⟨hBsq, herr, herr.trans ?_⟩
  calc
    2 * ε / (1 + ε) + |B θ| * r ≤ 2 * ε / (1 + ε) + r ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hB hr0]
    _ = 2 * ε / (1 + ε) + 4 * ε / (1 + ε) ^ 2 := by rw [hrsq]
    _ ≤ 2 * ε + 4 * ε := by
      exact add_le_add (div_le_self (by positivity) hd1)
        (div_le_self (by positivity) (by nlinarith))
    _ = 6 * ε := by ring

#print axioms solution
