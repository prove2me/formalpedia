-- Prove2me | solution 1 for WilliamsonShmoys.finite_preorder_maximal_extension__p2m_8fa7b5e9_9ae2_4561_bc62_ceb5c7ac1a09_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:57:18.652575+00:00
-- url     : https://prove2.me/submissions/ef829b44-d907-480c-8a7a-5efa8a552223

import Mathlib
set_option autoImplicit false

theorem solution
    {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop) (x : α) (hx : P x) :
    ∃ y : α, x ≤ y ∧ P y ∧
      (∀ z : α, y ≤ z → P z → z ≤ y) := by
  obtain ⟨y, hxy, hymax⟩ := Finite.exists_le_maximal (p := P) hx
  refine ⟨y, hxy, hymax.1, ?_⟩
  intro z hyz hPz
  exact hymax.2 hPz hyz