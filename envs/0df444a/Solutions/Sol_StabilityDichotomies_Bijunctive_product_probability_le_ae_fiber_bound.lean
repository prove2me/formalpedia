-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.product_probability_le_ae_fiber_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:50:36.053437+00:00
-- url     : https://prove2.me/submissions/e630accb-648c-41f0-81f1-b28352b46a6a

import Mathlib
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Set Filter

theorem solution {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [SFinite ν]
    (E : Set (α × β)) (hE : MeasurableSet E) (c : ℝ≥0∞)
    (hbound : ∀ᵐ x ∂μ, ν {y | (x,y) ∈ E} ≤ c) :
    (μ.prod ν) E ≤ c := by
  rw [Measure.prod_apply hE]
  calc
    ∫⁻ x, ν (Prod.mk x ⁻¹' E) ∂μ ≤ ∫⁻ _x, c ∂μ := lintegral_mono_ae hbound
    _ = c := by simp
