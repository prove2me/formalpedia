-- Prove2me | solution 1 for Rudin.ch11_monotone_convergence
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:42:37.859139+00:00
-- url     : https://prove2.me/submissions/b874b4bd-6138-4311-9e60-7563d5e8ce19

import Mathlib
import Definitions.Def_Rudin_ch11_L2
open Filter Topology MeasureTheory Rudin
open scoped ENNReal
set_option maxHeartbeats 1000000
set_option autoImplicit false
/-- Rudin, Theorem 11.28 (Lebesgue's monotone convergence theorem): if `0 ≤ f 0 ≤ f 1 ≤ ⋯` are
measurable and converge pointwise to `g`, then the integrals converge to the integral of
`g`. -/
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) (hmono : ∀ x, Monotone fun n => f n x)
    (g : X → ℝ≥0∞) (hg : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 (∫⁻ x, g x ∂μ)) := by
  exact lintegral_tendsto_of_tendsto_of_monotone (fun n => (hf n).aemeasurable)
    (Filter.Eventually.of_forall hmono) (Filter.Eventually.of_forall hg)

#print axioms solution
