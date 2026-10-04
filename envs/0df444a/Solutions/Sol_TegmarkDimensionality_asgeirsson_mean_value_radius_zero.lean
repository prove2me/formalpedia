-- Prove2me | solution 1 for TegmarkDimensionality.asgeirsson_mean_value_radius_zero
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T05:17:02.923817+00:00
-- url     : https://prove2.me/submissions/c98e063d-b78f-422a-8d98-5a1204ac73ea

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
