-- Prove2me | solution 1 for Rudin.ch11_dominated_convergence
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:42:41.652357+00:00
-- url     : https://prove2.me/submissions/45818b2b-10f7-4be8-93a6-c9b5158ad247

import Mathlib
import Definitions.Def_Rudin_ch11_L2
open Filter Topology MeasureTheory Rudin
open scoped ENNReal
set_option maxHeartbeats 1000000
set_option autoImplicit false
/-- Rudin, Theorem 11.32 (Lebesgue's dominated convergence theorem): if measurable functions
`f n` converge pointwise to `g` and are dominated by an integrable `h`, then `g` is
integrable and the integrals converge. -/
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℝ) (g h : X → ℝ) (hf : ∀ n, Measurable (f n))
    (hdom : ∀ n, ∀ x, |f n x| ≤ h x) (hh : Integrable h μ)
    (hconv : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Integrable g μ ∧ Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  have hg : Measurable g := measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.2 hconv)
  have hb : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ h x := fun n =>
    Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hdom n x)
  have hgb : ∀ x, ‖g x‖ ≤ h x := by
    intro x
    exact le_of_tendsto (hconv x |>.norm) (Filter.Eventually.of_forall (fun n => by
      simpa only [Real.norm_eq_abs] using hdom n x))
  exact ⟨hh.mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall hgb),
    tendsto_integral_of_dominated_convergence h (fun n => (hf n).aestronglyMeasurable) hh hb
      (Filter.Eventually.of_forall hconv)⟩

#print axioms solution
