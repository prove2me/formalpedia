-- Prove2me | solution 1 for WeightedRootIntegralIdentity.upper_boundary_dominated_convergence_v4
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T09:50:48.484122+00:00
-- url     : https://prove2.me/submissions/c2ef5cbf-5550-486b-949d-7e0a40999d30

import Mathlib
open MeasureTheory Filter
open scoped Topology

theorem solution {f : ℕ → ℝ → ℂ} {f₀ : ℝ → ℂ} {g : ℝ → ℝ} {μ : Measure ℝ}
    (hG : Integrable g μ)
    (hmeas : ∀ n, AEStronglyMeasurable (f n) μ)
    (hdom : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f₀ x))) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, f₀ x ∂μ)) := by
  exact MeasureTheory.tendsto_integral_of_dominated_convergence g hmeas hG hdom hlim
