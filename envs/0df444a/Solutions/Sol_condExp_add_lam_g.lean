-- Prove2me | solution 1 for condExp_add_lam_g
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T19:46:06.563985+00:00
-- url     : https://prove2.me/submissions/50aba981-bd04-4e20-a755-4474da5f5218

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology

theorem solution {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[fun ω => f ω + g ω | m] =ᵐ[μ] μ[f | m] + μ[g | m] := by
  have h := condExp_add hf hg m
  have h1 : μ[f + g | m] =ᵐ[μ] μ[fun ω => f ω + g ω | m] :=
    condExp_congr_ae (m := m) (Filter.EventuallyEq.of_eq (by funext ω; rfl))
  have h2 : μ[fun ω => f ω + g ω | m] =ᵐ[μ] μ[f | m] + μ[g | m] := h1.symm.trans h
  filter_upwards [h2] with ω hω
  rw [hω]
