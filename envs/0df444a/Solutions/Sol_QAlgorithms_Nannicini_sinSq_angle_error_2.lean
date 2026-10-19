-- Prove2me | solution 2 for QAlgorithms.Nannicini.sinSq_angle_error
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-17T21:25:23.368285+00:00
-- url     : https://prove2.me/submissions/317cc17d-df37-43bb-9cca-c6c340a778e7

import Mathlib

set_option autoImplicit false

theorem solution (θ θt ε : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 2 * Real.pi)
    (hθt0 : 0 ≤ θt) (hθt1 : θt ≤ 2 * Real.pi) (h : |θ - θt| ≤ ε) :
    |Real.sin θ ^ 2 - Real.sin θt ^ 2| ≤
      2 * ε * Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) + ε ^ 2 := by
  obtain ⟨δ, rfl⟩ : ∃ δ, θt = θ + δ := ⟨θt - θ, by ring⟩
  have hδ : |δ| ≤ ε := by
    have : θ - (θ + δ) = -δ := by ring
    rwa [this, abs_neg] at h
  have hs := Real.sin_sq_add_cos_sq θ
  have hd := Real.sin_sq_add_cos_sq δ
  have key : Real.sin θ ^ 2 - Real.sin (θ + δ) ^ 2 =
      -(Real.sin δ * Real.cos δ * Real.sin (2 * θ) + Real.sin δ ^ 2 * Real.cos (2 * θ)) := by
    rw [Real.sin_add, Real.sin_two_mul, Real.cos_two_mul]
    linear_combination (-(Real.sin θ) ^ 2) * hd + (Real.sin δ ^ 2) * hs
  have hsq : Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) = |Real.sin θ * Real.cos θ| := by
    have : Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2) = (Real.sin θ * Real.cos θ) ^ 2 := by
      have : 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by linarith
      rw [this]; ring
    rw [this, Real.sqrt_sq_eq_abs]
  rw [key, abs_neg, hsq]
  have h1 : |Real.sin δ| ≤ ε := (Real.abs_sin_le_abs).trans hδ
  have h2 : |Real.cos δ| ≤ 1 := Real.abs_cos_le_one δ
  have h3 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have h4 : |Real.sin (2 * θ)| = 2 * |Real.sin θ * Real.cos θ| := by
    rw [Real.sin_two_mul, abs_mul, abs_mul, abs_mul]; norm_num; ring
  have hε : 0 ≤ ε := (abs_nonneg _).trans hδ
  have h5 : 0 ≤ |Real.sin δ| := abs_nonneg _
  have h6 : 0 ≤ |Real.sin θ * Real.cos θ| := abs_nonneg _
  calc |Real.sin δ * Real.cos δ * Real.sin (2 * θ) + Real.sin δ ^ 2 * Real.cos (2 * θ)|
      ≤ |Real.sin δ * Real.cos δ * Real.sin (2 * θ)| + |Real.sin δ ^ 2 * Real.cos (2 * θ)| :=
        abs_add_le _ _
    _ = |Real.sin δ| * |Real.cos δ| * |Real.sin (2 * θ)| + |Real.sin δ| ^ 2 * |Real.cos (2 * θ)| := by
        rw [abs_mul, abs_mul, abs_mul, abs_pow]
    _ ≤ ε * 1 * (2 * |Real.sin θ * Real.cos θ|) + ε ^ 2 * 1 := by
        rw [h4]
        gcongr
    _ = 2 * ε * |Real.sin θ * Real.cos θ| + ε ^ 2 := by ring
