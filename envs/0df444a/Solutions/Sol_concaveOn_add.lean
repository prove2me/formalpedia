-- Prove2me | solution 1 for concaveOn_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:23:19.603984+00:00
-- url     : https://prove2.me/submissions/506169f4-6fcc-43fc-9455-79d078b991bd

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : ConcaveOn ℝ s f) (hg : ConcaveOn ℝ s g) :
    ConcaveOn ℝ s (fun x => f x + g x) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy u v hu hv huv
  have h₁ := hf.2 hx hy hu hv huv
  have h₂ := hg.2 hx hy hu hv huv
  dsimp at h₁ h₂ ⊢
  nlinarith [h₁, h₂]
