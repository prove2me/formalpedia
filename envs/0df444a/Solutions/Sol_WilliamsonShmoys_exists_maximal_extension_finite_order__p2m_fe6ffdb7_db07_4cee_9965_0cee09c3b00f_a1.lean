-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_extension_finite_order__p2m_fe6ffdb7_db07_4cee_9965_0cee09c3b00f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:05:41.472274+00:00
-- url     : https://prove2.me/submissions/77c269c1-1e08-4602-9134-c0bcb39e772b

import Mathlib

theorem solution {α : Type} [Fintype α] [PartialOrder α] (Q : α → Prop) (x : α) (hx : Q x) :
    ∃ y : α, x ≤ y ∧ Q y ∧ ∀ z : α, y ≤ z → Q z → z ≤ y := by
  classical
  obtain ⟨y, hxy, hymax⟩ :=
    (Set.toFinite {y : α | Q y}).exists_le_maximal (a := x) (by simpa using hx)
  rcases hymax with ⟨hy, hmax⟩
  refine ⟨y, hxy, hy, ?_⟩
  intro z hyz hz
  exact hmax hz hyz