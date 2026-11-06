-- Prove2me | solution 1 for comp_exp_support2
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:27:33.838208+00:00
-- url     : https://prove2.me/submissions/ae57e8f7-6fb4-41ff-a590-a5db43073d90

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

open Real Filter Set

theorem solution {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ) :
    ∀ᶠ (x : ℝ) in atTop, (Ψ ∘ rexp) x = 0 := by
  obtain ⟨b, hb⟩ := hsupp.isCompact.bddAbove
  filter_upwards [Real.tendsto_exp_atTop.eventually (eventually_gt_atTop b)] with x hx
  change Ψ (rexp x) = 0
  exact image_eq_zero_of_notMem_tsupport (fun h ↦ (not_le_of_gt hx) (hb h))
