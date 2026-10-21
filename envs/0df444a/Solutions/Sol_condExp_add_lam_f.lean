-- Prove2me | solution 1 for condExp_add_lam_f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T19:30:57.480453+00:00
-- url     : https://prove2.me/submissions/f2d02947-f405-431d-afa5-d9b687f563c3

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology

theorem solution {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[fun ω => f ω + g ω | m] =ᵐ[μ] μ[f | m] + μ[g | m] := by
  have h := condExp_add hf hg m
  have h1 : μ[f + g | m] =ᵐ[μ] μ[fun ω => f ω + g ω | m] :=
    condExp_congr_ae (m := m) (Filter.EventuallyEq.of_eq (by funext ω; rfl))
  have h2 : μ[fun ω => f ω + g ω | m] =ᵐ[μ] μ[f | m] + μ[g | m] := h1.symm.trans h
  filter_upwards [h2] with ω hω
  rw [hω]
