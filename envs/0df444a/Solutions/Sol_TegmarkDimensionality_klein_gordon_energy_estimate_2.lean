-- Prove2me | solution 2 for TegmarkDimensionality.klein_gordon_energy_estimate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T05:34:07.644981+00:00
-- url     : https://prove2.me/submissions/73c66493-e40d-43f9-b9b5-af472aa958e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_tegmark_laplacian
import Theorems.Thm_TegmarkDimensionality_klein_gordon_energy_estimate_initial_time
import Theorems.Thm_TegmarkDimensionality_klein_gordon_energy_estimate_light_cone
import Theorems.Thm_TegmarkDimensionality_klein_gordon_energy_estimate_interior
import Mathlib

open MeasureTheory TegmarkDimensionality

theorem solution (n : ℕ) (μ : ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ContDiff ℝ 2 (fun p : ℝ × EuclideanSpace ℝ (Fin n) => u p.1 p.2))
    (hKG : ∀ t x, deriv (fun s => deriv (fun s' => u s' x) s) t =
      laplacian (u t) x - μ ^ 2 * u t x)
    (x₀ : EuclideanSpace ℝ (Fin n)) (R t : ℝ) (ht : |t| ≤ R) :
    ∫ x in Metric.ball x₀ (R - |t|),
        ((deriv (fun s => u s x) t) ^ 2 + ‖fderiv ℝ (u t) x‖ ^ 2 + μ ^ 2 * (u t x) ^ 2) ≤
      ∫ x in Metric.ball x₀ R,
        ((deriv (fun s => u s x) 0) ^ 2 + ‖fderiv ℝ (u 0) x‖ ^ 2 + μ ^ 2 * (u 0 x) ^ 2) := by
  rcases eq_or_ne t 0 with rfl | ht0
  · exact klein_gordon_energy_estimate_initial_time n μ u hu hKG x₀ R 0 ht rfl
  · by_cases htR : |t| = R
    · exact klein_gordon_energy_estimate_light_cone n μ u hu hKG x₀ R t ht htR
    have hint : 0 < |t| ∧ |t| < R :=
      ⟨abs_pos.mpr ht0, lt_of_le_of_ne ht htR⟩
    exact klein_gordon_energy_estimate_interior n μ u hu hKG x₀ R t ht hint
