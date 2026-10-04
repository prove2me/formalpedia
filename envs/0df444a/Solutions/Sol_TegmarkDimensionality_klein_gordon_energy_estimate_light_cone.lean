-- Prove2me | solution 1 for TegmarkDimensionality.klein_gordon_energy_estimate_light_cone
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T04:19:23.644133+00:00
-- url     : https://prove2.me/submissions/aa745e56-5451-49dd-a240-1b2b40190ff6

import Definitions.Def_tegmark_laplacian
import Mathlib

open MeasureTheory TegmarkDimensionality Metric

/-- On the light cone `|t| = R`, the domain `B(x₀, R - |t|)` is empty, so the left-hand
energy integral is zero and bounded by the nonnegative initial energy on `B(x₀, R)`. -/
theorem solution (n : ℕ) (μ : ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (_hu : ContDiff ℝ 2 (fun p : ℝ × EuclideanSpace ℝ (Fin n) => u p.1 p.2))
    (_hKG : ∀ t x, deriv (fun s => deriv (fun s' => u s' x) s) t =
      laplacian (u t) x - μ ^ 2 * u t x)
    (x₀ : EuclideanSpace ℝ (Fin n)) (R t : ℝ) (_ht : |t| ≤ R) (htR : |t| = R) :
    ∫ x in ball x₀ (R - |t|),
        ((deriv (fun s => u s x) t) ^ 2 + ‖fderiv ℝ (u t) x‖ ^ 2 + μ ^ 2 * (u t x) ^ 2) ≤
      ∫ x in ball x₀ R,
        ((deriv (fun s => u s x) 0) ^ 2 + ‖fderiv ℝ (u 0) x‖ ^ 2 + μ ^ 2 * (u 0 x) ^ 2) := by
  have hsub : R - |t| = 0 := by rw [htR, sub_self]
  rw [hsub, ball_zero, setIntegral_empty]
  refine setIntegral_nonneg measurableSet_ball ?_
  intro x _
  nlinarith [sq_nonneg (deriv (fun s => u s x) 0), sq_nonneg ‖fderiv ℝ (u 0) x‖,
    sq_nonneg (μ * u 0 x)]
