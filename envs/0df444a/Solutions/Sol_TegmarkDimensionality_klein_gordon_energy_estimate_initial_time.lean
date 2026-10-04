-- Prove2me | solution 1 for TegmarkDimensionality.klein_gordon_energy_estimate_initial_time
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T03:28:41.139463+00:00
-- url     : https://prove2.me/submissions/c0d52855-c40b-4416-aff4-6c12b7ef3ed1

import Definitions.Def_tegmark_laplacian
import Mathlib

open MeasureTheory TegmarkDimensionality Metric

/-- At `t = 0`, the Klein–Gordon energy on the ball of radius `R` equals the initial
energy on the same ball (the finite-speed bound is tight at the initial time). -/
theorem solution (n : ℕ) (μ : ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ContDiff ℝ 2 (fun p : ℝ × EuclideanSpace ℝ (Fin n) => u p.1 p.2))
    (hKG : ∀ t x, deriv (fun s => deriv (fun s' => u s' x) s) t =
      laplacian (u t) x - μ ^ 2 * u t x)
    (x₀ : EuclideanSpace ℝ (Fin n)) (R t : ℝ) (_ht : |t| ≤ R) (ht0 : t = 0) :
    ∫ x in ball x₀ (R - |t|),
        ((deriv (fun s => u s x) t) ^ 2 + ‖fderiv ℝ (u t) x‖ ^ 2 + μ ^ 2 * (u t x) ^ 2) ≤
      ∫ x in ball x₀ R,
        ((deriv (fun s => u s x) 0) ^ 2 + ‖fderiv ℝ (u 0) x‖ ^ 2 + μ ^ 2 * (u 0 x) ^ 2) := by
  subst ht0
  simp only [abs_zero, sub_zero, le_refl]
