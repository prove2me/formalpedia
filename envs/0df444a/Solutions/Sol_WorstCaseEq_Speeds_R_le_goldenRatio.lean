-- Prove2me | solution 1 for WorstCaseEq.Speeds.R_le_goldenRatio
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T07:07:43.961973+00:00
-- url     : https://prove2.me/submissions/b14d6baf-9115-4a3c-b264-48da81035b67

import Mathlib

open Real

theorem solution (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂)
    (hφ : s₂ ≤ goldenRatio * s₁) :
    1 + s₂ / (s₁ + s₂) ≤ goldenRatio ∧
      (s₂ = goldenRatio * s₁ → 1 + s₂ / (s₁ + s₂) = goldenRatio) := by
  have hden : 0 < s₁ + s₂ := by linarith
  have hne : goldenRatio ≠ 0 := goldenRatio_ne_zero
  have hs : s₁ ≠ 0 := ne_of_gt h₁
  have hsq : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have hr : (goldenRatio * s₁) / (s₁ + goldenRatio * s₁) = goldenRatio⁻¹ := by
    have : s₁ + goldenRatio * s₁ = s₁ * goldenRatio ^ 2 := by
      rw [hsq]; ring
    rw [this]
    field_simp [hs, hne]
  have hone : 1 + goldenRatio⁻¹ = goldenRatio := by
    calc
      1 + goldenRatio⁻¹ = (goldenRatio + 1) * goldenRatio⁻¹ := by field_simp [hne]
      _ = goldenRatio ^ 2 * goldenRatio⁻¹ := by rw [← hsq]
      _ = goldenRatio := by field_simp [hne]
  have hdenφ : 0 < s₁ + goldenRatio * s₁ := by
    have := goldenRatio_pos; positivity
  have hle : s₂ / (s₁ + s₂) ≤ (goldenRatio * s₁) / (s₁ + goldenRatio * s₁) := by
    rw [div_le_div_iff₀ hden hdenφ]
    nlinarith [hφ]
  constructor
  · rw [hr] at hle
    linarith
  · intro heq
    rw [heq, hr, hone]
