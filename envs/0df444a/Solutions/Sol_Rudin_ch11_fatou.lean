-- Prove2me | solution 1 for Rudin.ch11_fatou
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:42:39.9845+00:00
-- url     : https://prove2.me/submissions/39fc986b-04a3-40a8-8423-1569731d430a

import Mathlib
import Definitions.Def_Rudin_ch11_L2
open Filter Topology MeasureTheory Rudin
open scoped ENNReal
set_option maxHeartbeats 1000000
set_option autoImplicit false
/-- Rudin, Theorem 11.31 (Fatou's theorem): for nonnegative measurable functions, the integral of
the lower limit is at most the lower limit of the integrals. -/
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) :
    (∫⁻ x, liminf (fun n => f n x) atTop ∂μ) ≤ liminf (fun n => ∫⁻ x, f n x ∂μ) atTop := by
  exact lintegral_liminf_le hf

#print axioms solution
