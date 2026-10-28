-- Prove2me | solution 2 for WilliamsonShmoys.card_subtype_lt_of_subset_of_new
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:07:57.409043+00:00
-- url     : https://prove2.me/submissions/818d9034-63a6-413c-9a70-d1e8b2ac6f60

import Mathlib

set_option autoImplicit false
theorem solution
    {α : Type} [Fintype α] (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hsubset : ∀ x : α, P x → Q x)
    (a : α) (haQ : Q a) (haP : ¬ P a) :
    Fintype.card {x : α // P x} < Fintype.card {x : α // Q x} := by
  rw [Fintype.card_subtype, Fintype.card_subtype]
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hsubset x hx
  · have := h (by simp [haQ] : a ∈ Finset.univ.filter Q); simp at this; exact haP this
