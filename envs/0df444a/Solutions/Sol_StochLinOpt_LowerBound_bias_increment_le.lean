-- Prove2me | solution 1 for StochLinOpt.LowerBound.bias_increment_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:40:40.462491+00:00
-- url     : https://prove2.me/submissions/c7c6bcce-1a38-4d56-9e77-5a7d283491db

import Mathlib
import Definitions.Def_StochLinOpt_LowerBound_circleBandit

open Matrix

namespace StochLinOpt.LowerBound

theorem aux_bil_cs (μ x : Fin 2 → ℝ) (hμ : μ ⬝ᵥ μ = 1 / 4) (hx : x ⬝ᵥ x = 1) :
    (μ ⬝ᵥ x) ^ 2 ≤ 1 / 4 := by
  simp only [dotProduct, Fin.sum_univ_two] at *
  nlinarith [sq_nonneg (μ 0 * x 1 - μ 1 * x 0)]

theorem aux_bil_abs (μ x : Fin 2 → ℝ) (hμ : μ ⬝ᵥ μ = 1 / 4) (hx : x ⬝ᵥ x = 1) :
    |μ ⬝ᵥ x| ≤ 1 / 2 := by
  have h := aux_bil_cs μ x hμ hx
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (μ ⬝ᵥ x - 1/2), sq_nonneg (μ ⬝ᵥ x + 1/2)]

end StochLinOpt.LowerBound

open StochLinOpt.LowerBound
open Matrix

theorem solution (μ₁ μ₂ x : Fin 2 → ℝ) (p ℓ : ℝ)
    (hμ₁ : μ₁ ⬝ᵥ μ₁ = 1 / 4) (hμ₂ : μ₂ ⬝ᵥ μ₂ = 1 / 4) (hx : x ∈ unitCircle)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hℓ : ℓ = 1 ∨ ℓ = -1) :
    |biasUpdate μ₁ μ₂ x p ℓ - (2 * p - 1)| ≤ |(μ₁ - μ₂) ⬝ᵥ x| := by
  have hx' : x ⬝ᵥ x = 1 := hx
  have ha := aux_bil_abs μ₁ x hμ₁ hx'
  have hb := aux_bil_abs μ₂ x hμ₂ hx'
  rw [sub_dotProduct]
  unfold biasUpdate
  set a := μ₁ ⬝ᵥ x with ha_def
  set b := μ₂ ⬝ᵥ x with hb_def
  rw [abs_le] at ha hb
  have hD : 1 / 2 ≤ p * (1 + ℓ * a) + (1 - p) * (1 + ℓ * b) := by
    rcases hℓ with rfl | rfl <;> nlinarith
  have hDpos : 0 < p * (1 + ℓ * a) + (1 - p) * (1 + ℓ * b) := by linarith
  have key : (p * (1 + ℓ * a) - (1 - p) * (1 + ℓ * b)) /
      (p * (1 + ℓ * a) + (1 - p) * (1 + ℓ * b)) - (2 * p - 1)
      = (2 * p * (1 - p) * ℓ * (a - b)) / (p * (1 + ℓ * a) + (1 - p) * (1 + ℓ * b)) := by
    field_simp
    ring
  rw [key, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
  have hℓabs : |ℓ| = 1 := by rcases hℓ with rfl | rfl <;> simp
  rw [abs_mul, abs_mul, hℓabs, mul_one]
  have hpp : 0 ≤ 2 * p * (1 - p) := by nlinarith
  rw [abs_of_nonneg hpp]
  have hpp2 : 2 * p * (1 - p) ≤ 1 / 2 := by nlinarith [sq_nonneg (p - 1/2)]
  have habs : 0 ≤ |a - b| := abs_nonneg _
  nlinarith
