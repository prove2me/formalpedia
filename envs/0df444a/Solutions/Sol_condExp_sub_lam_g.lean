-- Prove2me | solution 1 for condExp_sub_lam_g
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T19:46:14.115875+00:00
-- url     : https://prove2.me/submissions/efabddab-06d1-4fc4-b074-a681ac7708a3

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology

theorem solution {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[fun ω => f ω - g ω | m] =ᵐ[μ] μ[f | m] - μ[g | m] := by
  have h := condExp_sub hf hg m
  have h1 : μ[f - g | m] =ᵐ[μ] μ[fun ω => f ω - g ω | m] :=
    condExp_congr_ae (m := m) (Filter.EventuallyEq.of_eq (by funext ω; rfl))
  have h2 : μ[fun ω => f ω - g ω | m] =ᵐ[μ] μ[f | m] - μ[g | m] := h1.symm.trans h
  filter_upwards [h2] with ω hω
  rw [hω]
