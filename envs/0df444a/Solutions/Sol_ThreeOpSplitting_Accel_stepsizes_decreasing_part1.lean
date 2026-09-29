-- Prove2me | solution 1 for ThreeOpSplitting.Accel.stepsizes_decreasing_part1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T05:18:21.156311+00:00
-- url     : https://prove2.me/submissions/e51ddce0-c07e-4233-8de9-052ea0a6a780

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_Stepsizes

open Filter Topology
open ThreeOpSplitting.Accel

/-- Any `γ` with `2aγ = -b + s`, `s² = b² + 4ag²` satisfies `aγ² + bγ = g²`. -/
private theorem root_alg2 (a b g s γ : ℝ) (ha : 0 < a) (hs2 : s ^ 2 = b ^ 2 + 4 * a * g ^ 2)
    (hlin : 2 * a * γ = -b + s) : a * γ ^ 2 + b * γ = g ^ 2 := by
  have e1 : 4 * a ^ 2 * γ ^ 2 = 2 * b ^ 2 - 2 * b * s + 4 * a * g ^ 2 := by
    linear_combination (2 * a * γ + (-b + s)) * hlin + hs2
  have e2 : 4 * a * b * γ = -2 * b ^ 2 + 2 * b * s := by
    linear_combination 2 * b * hlin
  have key : 4 * a * (a * γ ^ 2 + b * γ) = 4 * a * g ^ 2 := by linear_combination e1 + e2
  exact mul_left_cancel₀ (by positivity) key

/-- `(-b + √(b² + 4ag²))/(2a)` is the positive root of `aγ² + bγ - g² = 0`. -/
private theorem root_alg (a b g : ℝ) (ha : 0 < a) :
    a * ((-b + Real.sqrt (b ^ 2 + 4 * a * g ^ 2)) / (2 * a)) ^ 2
      + b * ((-b + Real.sqrt (b ^ 2 + 4 * a * g ^ 2)) / (2 * a)) = g ^ 2 := by
  have hag : 0 ≤ a * g ^ 2 := mul_nonneg ha.le (sq_nonneg g)
  have hD : (0:ℝ) ≤ b ^ 2 + 4 * a * g ^ 2 := by nlinarith [sq_nonneg b]
  have ha2 : (2 * a) ≠ 0 := by positivity
  refine root_alg2 a b g (Real.sqrt (b ^ 2 + 4 * a * g ^ 2)) _ ha (Real.sq_sqrt hD) ?_
  field_simp

private theorem sp1_pos (μB μC η γ0 : ℝ) (hμB : 0 ≤ μB) (hμC : 0 < μC) (hη0 : 0 < η)
    (hγ0 : 0 < γ0) : ∀ k, 0 < stepsPart1 μB μC η γ0 k := by
  intro k
  induction k with
  | zero => exact hγ0
  | succ k ih =>
    have ha : 0 < 1 + 2 * stepsPart1 μB μC η γ0 k * μB := by nlinarith
    have hb : 0 ≤ 2 * stepsPart1 μB μC η γ0 k ^ 2 * μC * η := by positivity
    have h4 : 0 < 4 * (1 + 2 * stepsPart1 μB μC η γ0 k * μB) * stepsPart1 μB μC η γ0 k ^ 2 :=
      mul_pos (by linarith) (by positivity)
    have hD : (2 * stepsPart1 μB μC η γ0 k ^ 2 * μC * η) ^ 2
        < (2 * stepsPart1 μB μC η γ0 k ^ 2 * μC * η) ^ 2
          + 4 * (1 + 2 * stepsPart1 μB μC η γ0 k * μB) * stepsPart1 μB μC η γ0 k ^ 2 := by
      linarith
    have hs : 2 * stepsPart1 μB μC η γ0 k ^ 2 * μC * η
        < Real.sqrt ((2 * stepsPart1 μB μC η γ0 k ^ 2 * μC * η) ^ 2
          + 4 * (1 + 2 * stepsPart1 μB μC η γ0 k * μB) * stepsPart1 μB μC η γ0 k ^ 2) := by
      have h1 := Real.sqrt_lt_sqrt (by positivity) hD
      rwa [Real.sqrt_sq hb] at h1
    have heq : stepsPart1 μB μC η γ0 (k + 1) =
        (-2 * stepsPart1 μB μC η γ0 k ^ 2 * μC * η +
          Real.sqrt ((2 * stepsPart1 μB μC η γ0 k ^ 2 * μC * η) ^ 2
            + 4 * (1 + 2 * stepsPart1 μB μC η γ0 k * μB) * stepsPart1 μB μC η γ0 k ^ 2))
          / (2 * (1 + 2 * stepsPart1 μB μC η γ0 k * μB)) := rfl
    rw [heq]
    exact div_pos (by linarith) (by linarith)

/-- `γ_{k+1}` is the positive root of `(1 + 2γ_kμ_B)γ² + 2γ_k²μ_Cη·γ - γ_k² = 0`. -/
private theorem sp1_root (μB μC η γ0 : ℝ) (hμB : 0 ≤ μB) (hμC : 0 < μC) (hη0 : 0 < η)
    (hγ0 : 0 < γ0) (k : ℕ) :
    (1 + 2 * stepsPart1 μB μC η γ0 k * μB) * stepsPart1 μB μC η γ0 (k + 1) ^ 2
      + 2 * stepsPart1 μB μC η γ0 k ^ 2 * μC * η * stepsPart1 μB μC η γ0 (k + 1)
      = stepsPart1 μB μC η γ0 k ^ 2 := by
  have hgk := sp1_pos μB μC η γ0 hμB hμC hη0 hγ0 k
  have ha : 0 < 1 + 2 * stepsPart1 μB μC η γ0 k * μB := by nlinarith
  have heq0 : stepsPart1 μB μC η γ0 (k + 1) =
      (-2 * stepsPart1 μB μC η γ0 k ^ 2 * μC * η +
        Real.sqrt ((2 * stepsPart1 μB μC η γ0 k ^ 2 * μC * η) ^ 2
          + 4 * (1 + 2 * stepsPart1 μB μC η γ0 k * μB) * stepsPart1 μB μC η γ0 k ^ 2))
        / (2 * (1 + 2 * stepsPart1 μB μC η γ0 k * μB)) := rfl
  have heq : stepsPart1 μB μC η γ0 (k + 1) =
      (-(2 * stepsPart1 μB μC η γ0 k ^ 2 * μC * η) +
        Real.sqrt ((2 * stepsPart1 μB μC η γ0 k ^ 2 * μC * η) ^ 2
          + 4 * (1 + 2 * stepsPart1 μB μC η γ0 k * μB) * stepsPart1 μB μC η γ0 k ^ 2))
        / (2 * (1 + 2 * stepsPart1 μB μC η γ0 k * μB)) := by
    rw [heq0]; ring
  rw [heq]
  exact root_alg (1 + 2 * stepsPart1 μB μC η γ0 k * μB)
    (2 * stepsPart1 μB μC η γ0 k ^ 2 * μC * η) (stepsPart1 μB μC η γ0 k) ha

theorem solution (μB μC η γ0 : ℝ)
    (hμB : 0 ≤ μB) (hμC : 0 < μC) (hη0 : 0 < η) (hη1 : η < 1) (hγ0 : 0 < γ0) (k : ℕ) :
    0 < stepsPart1 μB μC η γ0 (k + 1) ∧
    stepsPart1 μB μC η γ0 k ^ 2 - stepsPart1 μB μC η γ0 (k + 1) ^ 2
      = stepsPart1 μB μC η γ0 k * stepsPart1 μB μC η γ0 (k + 1)
        * (2 * stepsPart1 μB μC η γ0 (k + 1) * μB + 2 * stepsPart1 μB μC η γ0 k * μC * η) ∧
    0 < stepsPart1 μB μC η γ0 k ^ 2 - stepsPart1 μB μC η γ0 (k + 1) ^ 2 := by
  have hgk := sp1_pos μB μC η γ0 hμB hμC hη0 hγ0 k
  have hgk1 := sp1_pos μB μC η γ0 hμB hμC hη0 hγ0 (k + 1)
  have hroot := sp1_root μB μC η γ0 hμB hμC hη0 hγ0 k
  refine ⟨hgk1, by nlinarith [hroot], ?_⟩
  have hprod : 0 < stepsPart1 μB μC η γ0 k * stepsPart1 μB μC η γ0 (k + 1)
      * (2 * stepsPart1 μB μC η γ0 (k + 1) * μB + 2 * stepsPart1 μB μC η γ0 k * μC * η) := by
    have h1 : 0 < 2 * stepsPart1 μB μC η γ0 k * μC * η := by positivity
    have h2 : 0 ≤ 2 * stepsPart1 μB μC η γ0 (k + 1) * μB := by positivity
    have : 0 < 2 * stepsPart1 μB μC η γ0 (k + 1) * μB + 2 * stepsPart1 μB μC η γ0 k * μC * η := by
      linarith
    positivity
  nlinarith [hroot]
