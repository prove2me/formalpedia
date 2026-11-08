-- Prove2me | solution 1 for QBFBackdoor.round_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:46:23.184528+00:00
-- url     : https://prove2.me/submissions/80df8e7e-c619-47ab-a866-ddf883369a41

import Mathlib

theorem solution (β : Type) [Fintype β] (a w : β → ℕ) (D : β → Prop)
    (F : ∀ b, (Fin (a b) → Bool) → (Fin (w b) → Bool) → Prop) (Dc : Prop)
    (hD : ∀ b, D b ↔ ∃ x, ∀ y, F b x y) :
    ((∃ b, D b) ∨ Dc) ↔
      ∃ x : ∀ b, Fin (a b) → Bool, ∀ y : ∀ b, Fin (w b) → Bool,
        (∃ b, F b (x b) (y b)) ∨ Dc := by
  classical
  constructor
  · rintro (⟨b, hb⟩ | hc)
    · obtain ⟨x0, hx0⟩ := (hD b).mp hb
      refine ⟨Function.update (fun b' (_ : Fin (a b')) => false) b x0,
        fun y => Or.inl ⟨b, ?_⟩⟩
      rw [Function.update_self]
      exact hx0 (y b)
    · exact ⟨fun _ _ => false, fun _ => Or.inr hc⟩
  · rintro ⟨x, hx⟩
    by_contra hcon
    have hnD : ∀ b, ¬ D b := fun b h => hcon (Or.inl ⟨b, h⟩)
    have hnc : ¬ Dc := fun h => hcon (Or.inr h)
    have hy : ∀ b, ∃ yb, ¬ F b (x b) yb := by
      intro b
      by_contra h
      apply hnD b
      rw [hD b]
      refine ⟨x b, fun yb => ?_⟩
      by_contra h'
      exact h ⟨yb, h'⟩
    choose y hy' using hy
    rcases hx y with ⟨b, hb⟩ | hc
    · exact hy' b hb
    · exact hnc hc
