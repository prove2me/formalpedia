-- Prove2me | solution 1 for condExp_mul_lam_g
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T19:46:23.198563+00:00
-- url     : https://prove2.me/submissions/3ff937b8-6c2a-4d08-a1b6-d4948562fdff

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology

theorem solution {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : AEStronglyMeasurable[m] f μ)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) :
    μ[fun ω => f ω * g ω | m] =ᵐ[μ] f * μ[g | m] := by
  have h := condExp_mul_of_aestronglyMeasurable_left (m := m) hf hfg hg
  have h1 : μ[f * g | m] =ᵐ[μ] μ[fun ω => f ω * g ω | m] :=
    condExp_congr_ae (m := m) (Filter.EventuallyEq.of_eq (by funext ω; rfl))
  have h2 : μ[fun ω => f ω * g ω | m] =ᵐ[μ] f * μ[g | m] := h1.symm.trans h
  filter_upwards [h2] with ω hω
  rw [hω]
