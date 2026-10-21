-- Prove2me | solution 1 for condExp_mul_lam_f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T19:31:10.924008+00:00
-- url     : https://prove2.me/submissions/ee004d94-8ce1-48d5-8d13-89ee2c156572

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology

theorem solution {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : AEStronglyMeasurable[m] f μ)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) :
    μ[fun ω => f ω * g ω | m] =ᵐ[μ] f * μ[g | m] := by
  have h := condExp_mul_of_aestronglyMeasurable_left (m := m) hf hfg hg
  have h1 : μ[f * g | m] =ᵐ[μ] μ[fun ω => f ω * g ω | m] :=
    condExp_congr_ae (m := m) (Filter.EventuallyEq.of_eq (by funext ω; rfl))
  have h2 : μ[fun ω => f ω * g ω | m] =ᵐ[μ] f * μ[g | m] := h1.symm.trans h
  filter_upwards [h2] with ω hω
  rw [hω]
