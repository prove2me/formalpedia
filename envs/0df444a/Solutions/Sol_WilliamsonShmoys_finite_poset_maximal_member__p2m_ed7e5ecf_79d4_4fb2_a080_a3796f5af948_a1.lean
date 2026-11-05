-- Prove2me | solution 1 for WilliamsonShmoys.finite_poset_maximal_member__p2m_ed7e5ecf_79d4_4fb2_a080_a3796f5af948_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:42:15.236586+00:00
-- url     : https://prove2.me/submissions/4bcd7117-c31e-47f9-b3bd-85a224383e39

import Mathlib

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (s : Set α) (hs : s.Nonempty) :
    ∃ a : α, s a ∧ ∀ b : α, s b → a ≤ b → b ≤ a := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, _, hb⟩ :=
    (Finite.exists_le_maximal (α := α) (p := s) (a := a) ha)
  exact ⟨b, hb.1, fun c hc hbc => hb.2 hc hbc⟩
