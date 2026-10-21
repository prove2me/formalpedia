-- Prove2me | solution 1 for condExp_mul_lam
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T19:03:16.24485+00:00
-- url     : https://prove2.me/submissions/fbf576fe-4ff8-4913-8719-e3f36f433c91

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology

theorem solution {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) :
    μ[fun ω => f ω * g ω | m] =ᵐ[μ] f * μ[g | m] := by
  have hmul := condExp_mul_of_aestronglyMeasurable_left (m := m) hf hfg hg
  have h1 : μ[f * g | m] =ᵐ[μ] μ[fun ω => f ω * g ω | m] :=
    condExp_congr_ae (m := m) (Filter.EventuallyEq.of_eq (by funext ω; rfl))
  have h2 : μ[fun ω => f ω * g ω | m] =ᵐ[μ] f * μ[g | m] := h1.symm.trans hmul
  filter_upwards [h2] with ω hω
  rw [hω]
