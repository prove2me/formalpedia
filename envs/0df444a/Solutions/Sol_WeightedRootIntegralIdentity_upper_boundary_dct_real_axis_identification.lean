-- Prove2me | solution 1 for WeightedRootIntegralIdentity.upper_boundary_dct_real_axis_identification
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T10:22:03.57927+00:00
-- url     : https://prove2.me/submissions/634475e8-7292-47f5-a734-c4c2a8894104

import Mathlib
open MeasureTheory Filter
open scoped Topology

theorem solution {f : ℕ → ℝ → ℂ} {f₀ h : ℝ → ℂ} {μ : Measure ℝ}
    (hDCT : Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, f₀ x ∂μ)))
    (hident : ∀ x, f₀ x = h x) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, h x ∂μ)) := by
  simpa [hident] using hDCT
