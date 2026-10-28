-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_above_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:14:42.504979+00:00
-- url     : https://prove2.me/submissions/b712d222-49b7-4f78-b6d4-ecba0b861608

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (a : α) (ha : P a) :
    ∃ m, P m ∧ a ≤ m ∧ ∀ n, m ≤ n → P n → n = m := by
  classical
  obtain ⟨m, ham, hm⟩ := Finite.exists_le_maximal (p := P) ha
  refine ⟨m, hm.1, ham, ?_⟩
  intro n hmn hn
  exact le_antisymm (hm.2 hn hmn) hmn