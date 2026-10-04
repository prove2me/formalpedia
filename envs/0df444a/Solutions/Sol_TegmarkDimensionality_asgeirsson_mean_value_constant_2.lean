-- Prove2me | solution 2 for TegmarkDimensionality.asgeirsson_mean_value_constant
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T05:34:07.105988+00:00
-- url     : https://prove2.me/submissions/0ea30fcb-a6b3-45e4-a51e-24c59e9879a4

import Definitions.Def_tegmark_laplacian
import Mathlib

open MeasureTheory TegmarkDimensionality Metric

theorem solution (n : ℕ) (c : ℝ)
    (u : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ) (_hu : ContDiff ℝ 2 u)
    (_hU : ∀ x y, laplacian (fun x' => u (x', y)) x = laplacian (fun y' => u (x, y')) y)
    (hconst : ∀ p, u p = c)
    (x₀ y₀ : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, u (x₀ + r • (ω : EuclideanSpace ℝ (Fin n)), y₀) ∂(volume.toSphere) =
      ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, u (x₀, y₀ + r • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere) := by
  simp only [hconst]
