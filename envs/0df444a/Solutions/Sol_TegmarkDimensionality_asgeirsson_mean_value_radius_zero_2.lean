-- Prove2me | solution 2 for TegmarkDimensionality.asgeirsson_mean_value_radius_zero
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T05:34:06.489341+00:00
-- url     : https://prove2.me/submissions/3b3620fb-b157-4349-a2a9-b4c7d1f67b7c

import Definitions.Def_tegmark_laplacian
import Mathlib

open MeasureTheory TegmarkDimensionality Metric

theorem solution (n : ℕ)
    (u : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ) (_hu : ContDiff ℝ 2 u)
    (_hU : ∀ x y, laplacian (fun x' => u (x', y)) x = laplacian (fun y' => u (x, y')) y)
    (x₀ y₀ : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : r = 0) :
    ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, u (x₀ + r • (ω : EuclideanSpace ℝ (Fin n)), y₀) ∂(volume.toSphere) =
      ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, u (x₀, y₀ + r • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere) := by
  subst hr
  simp only [zero_smul, add_zero]
