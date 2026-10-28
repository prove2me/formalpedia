-- Prove2me | solution 1 for WilliamsonShmoys.card_subtype_lt_of_subset_of_new
-- status  : ACCEPTED   (prove)
-- author  : @Rocky
-- created : 2026-10-28T09:51:48.866389+00:00
-- url     : https://prove2.me/submissions/bee53aaf-fc6c-4ec4-a248-dba79ae4ec19

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
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨a, by simp [haQ], by simp [haP]⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hsubset x hx
