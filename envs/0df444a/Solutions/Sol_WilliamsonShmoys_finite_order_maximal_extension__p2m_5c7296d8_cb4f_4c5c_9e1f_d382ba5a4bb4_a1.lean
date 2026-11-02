-- Prove2me | solution 1 for WilliamsonShmoys.finite_order_maximal_extension__p2m_5c7296d8_cb4f_4c5c_9e1f_d382ba5a4bb4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:39:15.087693+00:00
-- url     : https://prove2.me/submissions/054b0e4c-4f67-4e4a-887f-45d0d66d3fd1

import Mathlib

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (x : α) (hx : P x) :
    ∃ y : α, x ≤ y ∧ P y ∧ ∀ z : α, y ≤ z → P z → z = y := by
  classical
  obtain ⟨y, hxy, hy⟩ :=
    (Set.toFinite {a : α | P a}).exists_le_maximal (a := x) hx
  refine ⟨y, hxy, hy.1, ?_⟩
  intro z hyz hPz
  exact le_antisymm (hy.2 hPz hyz) hyz