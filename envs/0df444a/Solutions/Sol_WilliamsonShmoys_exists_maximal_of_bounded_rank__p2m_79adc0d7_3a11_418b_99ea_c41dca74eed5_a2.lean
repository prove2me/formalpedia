-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_of_bounded_rank__p2m_79adc0d7_3a11_418b_99ea_c41dca74eed5_a2
-- status  : ACCEPTED   (disprove)
-- author  : @garyholm
-- created : 2026-11-17T09:09:46.802672+00:00
-- url     : https://prove2.me/submissions/5eb2074a-ed96-4438-9562-e26ebe711939

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ {α : Type} (le : α → α → Prop) (Q : α → Prop) (r : α → Nat) (a : α) (ha : Q a) (hrefl : le a a) (B : Nat) (hbound : ∀ x : α, le a x → Q x → r x ≤ B) (hstrict : ∀ x y : α, le a x → Q x → le x y → Q y → x ≠ y → r x < r y), ∃ w : α, le a w ∧ Q w ∧ ∀ x : α, le w x → Q x → x = w) := by
  intro H
  let le : Fin 3 → Fin 3 → Prop := fun x y => y = x ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2)
  have h := @H (Fin 3) le (fun _ => True) (fun x => x.val) 0 trivial (Or.inl rfl) 1
    (by intro x hx _; simp only [le] at hx; omega)
    (by intro x y hx _ hxy _ hne; simp only [le] at hx hxy; omega)
  obtain ⟨w, hw, -, hmax⟩ := h
  simp only [le] at hw hmax
  rcases hw with rfl | ⟨-, rfl⟩ | ⟨h1, -⟩
  · have := hmax 1 (Or.inr (Or.inl ⟨rfl, rfl⟩)) trivial
    exact absurd this (by decide)
  · have := hmax 2 (Or.inr (Or.inr ⟨rfl, rfl⟩)) trivial
    exact absurd this (by decide)
  · exact absurd h1 (by decide)
