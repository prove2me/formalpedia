-- Prove2me | solution 1 for Rudin.ch11_integral_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:42:37.064253+00:00
-- url     : https://prove2.me/submissions/5ca66322-2130-43a0-93a4-a9f586c3fea0

import Mathlib
import Definitions.Def_Rudin_ch11_L2
open Filter Topology MeasureTheory Rudin
open scoped ENNReal
set_option maxHeartbeats 1000000
set_option autoImplicit false
/-- Rudin, Theorems 11.26 and 11.27: if `f` is integrable then so is `|f|` and
`|∫ f| ≤ ∫ |f|`; and a measurable function dominated by an integrable function is
integrable. -/
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ) :
    (Integrable f μ → Integrable (fun x => |f x|) μ ∧ |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ) ∧
    (Measurable f → Integrable g μ → (∀ x, |f x| ≤ g x) → Integrable f μ) := by
  constructor
  · intro hf
    exact ⟨hf.abs, by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm f⟩
  · intro hf hg hdom
    exact hg.mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hdom x))

#print axioms solution
