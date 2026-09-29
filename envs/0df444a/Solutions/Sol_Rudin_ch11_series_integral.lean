-- Prove2me | solution 1 for Rudin.ch11_series_integral
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:42:39.301987+00:00
-- url     : https://prove2.me/submissions/24717a30-89a7-4cb4-b7d6-42b38e07c596

import Mathlib
import Definitions.Def_Rudin_ch11_L2
open Filter Topology MeasureTheory Rudin
open scoped ENNReal
set_option maxHeartbeats 1000000
set_option autoImplicit false
/-- Rudin, Theorem 11.30: a series of nonnegative measurable functions may be integrated term by
term. -/
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) :
    (∫⁻ x, ∑' n, f n x ∂μ) = ∑' n, ∫⁻ x, f n x ∂μ := by
  exact lintegral_tsum (fun n => (hf n).aemeasurable)

#print axioms solution
