-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_of_finite_rank
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:30:24.595474+00:00
-- url     : https://prove2.me/submissions/2f205c8b-2f43-4ad6-880d-9a79a801fa71

import Mathlib
set_option autoImplicit false
theorem solution {α : Type} [Fintype α] (r : α → α → Prop) (P : α → Prop) (rank : α → Nat) (hstrict : ∀ a b, r a b → ¬ r b a → rank a < rank b) (hne : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → r a b → r b a := by
  classical
  obtain ⟨a, ha, hmax⟩ := (Finset.univ.filter P).exists_max_image rank
    (by obtain ⟨a, ha⟩ := hne; exact ⟨a, by simpa using ha⟩)
  refine ⟨a, by simpa using ha, fun b hb hab => ?_⟩
  by_contra h
  have := hstrict a b hab h
  have := hmax b (by simpa using hb)
  omega
