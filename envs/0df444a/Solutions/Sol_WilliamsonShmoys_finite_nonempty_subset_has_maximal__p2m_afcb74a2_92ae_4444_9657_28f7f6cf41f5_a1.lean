-- Prove2me | solution 1 for WilliamsonShmoys.finite_nonempty_subset_has_maximal__p2m_afcb74a2_92ae_4444_9657_28f7f6cf41f5_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:02:59.966625+00:00
-- url     : https://prove2.me/submissions/b5320c43-a530-458e-97aa-1ec3e8cb785e

import Mathlib
set_option autoImplicit false

theorem _root_.solution
    {α : Type} [PartialOrder α] [Finite α] (S : Set α)
    (hS : S.Finite) (hne : S.Nonempty) :
    ∃ a, a ∈ S ∧ ∀ b, b ∈ S → a ≤ b → b = a := by
  obtain ⟨a, ha⟩ := hS.exists_maximal hne
  exact ⟨a, ha.1, fun b hb hab => le_antisymm (ha.2 hb hab) hab⟩
