-- Prove2me | solution 1 for comp_exp_support1
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:27:13.110125+00:00
-- url     : https://prove2.me/submissions/856ef6f7-973c-4f6e-a8fd-123ee5c146d2

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

open Real Filter Set
open scoped Topology

theorem solution {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in atBot, Ψ (exp x) = 0 := by
  have h0 : (0 : ℝ) ∉ closure (Function.support Ψ) := by
    intro h
    have hpos : (0 : ℝ) < 0 := hplus h
    exact lt_irrefl 0 hpos
  have hnhd : (closure (Function.support Ψ))ᶜ ∈ 𝓝 (0 : ℝ) :=
    isClosed_closure.isOpen_compl.mem_nhds h0
  filter_upwards [Real.tendsto_exp_atBot.eventually hnhd] with x hx
  by_contra hne
  exact hx (subset_closure hne)
