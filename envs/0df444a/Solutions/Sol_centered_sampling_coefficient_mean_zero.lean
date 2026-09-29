-- Prove2me | solution 1 for centered_sampling_coefficient_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T20:52:07.026165+00:00
-- url     : https://prove2.me/submissions/f9e261b7-3e61-4dcb-af90-632aaab5c13f

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_bernoulli_powerset_expectation_linear
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 800000

/-- The coefficient statistic as a coordinate sum of inclusion-indicator
functions: `matrixEntrySum (centeredSamplingFluctuation Ω p B)
= ∑_w p⁻¹·B_w·(𝟙[w∈Ω] − p)`. -/
private theorem coeff_eq_linear {n₁ n₂ : ℕ}
    (p : ℝ) (B : Matrix (Fin n₁) (Fin n₂) ℝ)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    matrixEntrySum (centeredSamplingFluctuation Omega p B) =
      ∑ w : Fin n₁ × Fin n₂,
        (fun w' (x : ℝ) => p⁻¹ * (B w'.1 w'.2) * (x - p)) w
          (if w ∈ Omega then 1 else 0) := by
  classical
  unfold matrixEntrySum centeredSamplingFluctuation
  apply Finset.sum_congr rfl
  intro w _
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  unfold samplingProjection
  by_cases h : (w.1, w.2) ∈ Omega
  · simp only [h, if_true]; ring
  · simp only [h, if_false]; ring

/-- `centered_sampling_coefficient_mean_zero`.

**Mean zero**: the scalar centered sampling coefficient
`Coeff Ω = matrixEntrySum (centeredSamplingFluctuation Ω p B)
= ∑_{ij} p⁻¹(𝟙[(i,j)∈Ω] − p) B_{ij}` has Bernoulli-expectation zero (for `p ≠ 0`).
It is a sum of independent centered terms; by linearity of the powerset
expectation each coordinate contributes
`p·(p⁻¹B_w(1−p)) + (1−p)·(−B_w) = B_w(1−p) − (1−p)B_w = 0`. -/
theorem solution {n₁ n₂ : ℕ} (p : ℝ) (hp : p ≠ 0)
    (B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    bernoulliExpectation p
      (fun Omega => matrixEntrySum (centeredSamplingFluctuation Omega p B)) = 0 := by
  classical
  have hrw : (fun Omega : Finset (Fin n₁ × Fin n₂) =>
        matrixEntrySum (centeredSamplingFluctuation Omega p B)) =
      (fun Omega => ∑ w : Fin n₁ × Fin n₂,
        (fun w' (x : ℝ) => p⁻¹ * (B w'.1 w'.2) * (x - p)) w
          (if w ∈ Omega then 1 else 0)) := by
    funext Omega; exact coeff_eq_linear p B Omega
  rw [hrw]
  rw [bernoulli_powerset_expectation_linear (n₁ := n₁) (n₂ := n₂) p
      (fun w' (x : ℝ) => p⁻¹ * (B w'.1 w'.2) * (x - p))]
  apply Finset.sum_eq_zero
  intro w _
  have : p⁻¹ * p = 1 := inv_mul_cancel₀ hp
  field_simp
  ring
