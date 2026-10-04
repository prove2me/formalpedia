-- Prove2me | solution 1 for TegmarkDimensionality.asgeirsson_mean_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T05:17:05.397103+00:00
-- url     : https://prove2.me/submissions/f3b07f8b-55a3-4318-8183-90d84a51d4d9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_tegmark_laplacian
import Theorems.Thm_TegmarkDimensionality_asgeirsson_mean_value_radius_zero
import Theorems.Thm_TegmarkDimensionality_asgeirsson_mean_value_constant
import Theorems.Thm_TegmarkDimensionality_asgeirsson_mean_value_positive_radius
import Mathlib

open MeasureTheory TegmarkDimensionality Metric

theorem solution (n : ℕ)
    (u : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ) (hu : ContDiff ℝ 2 u)
    (hU : ∀ x y, laplacian (fun x' => u (x', y)) x = laplacian (fun y' => u (x, y')) y)
    (x₀ y₀ : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        u (x₀ + r • (ω : EuclideanSpace ℝ (Fin n)), y₀) ∂(volume.toSphere) =
      ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        u (x₀, y₀ + r • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere) := by
  rcases eq_or_ne r 0 with rfl | hrne
  · exact asgeirsson_mean_value_radius_zero n u hu hU x₀ y₀ 0 rfl
  by_cases hconst : ∃ c, ∀ p, u p = c
  · obtain ⟨c, hc⟩ := hconst
    exact asgeirsson_mean_value_constant n c u hu hU hc x₀ y₀ r
  · have hnc : ¬∀ (c : ℝ) (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)), u p = c := by
      rintro h
      have h0 := h 0 (x₀, y₀)
      have h1 := h 1 (x₀, y₀)
      norm_num at h0 h1
      linarith
    exact asgeirsson_mean_value_positive_radius n u hu hU x₀ y₀ r hrne hnc
