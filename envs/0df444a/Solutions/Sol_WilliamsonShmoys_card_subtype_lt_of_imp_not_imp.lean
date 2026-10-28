-- Prove2me | solution 1 for WilliamsonShmoys.card_subtype_lt_of_imp_not_imp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:41:31.088653+00:00
-- url     : https://prove2.me/submissions/b8fd8ad1-9a3e-4aa9-b9dc-7825a5a92637

import Mathlib

theorem solution
    {α : Type} [Fintype α] (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x, p x → q x)
    (hstrict : ∃ x, q x ∧ ¬ p x) :
    Fintype.card {x // p x} < Fintype.card {x // q x} := by
  rw [Fintype.card_subtype, Fintype.card_subtype]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (fun x hx => by simp at hx ⊢; exact hpq x hx)]
  obtain ⟨x, hq, hp⟩ := hstrict
  exact ⟨x, by simpa using hq, by simpa using hp⟩
