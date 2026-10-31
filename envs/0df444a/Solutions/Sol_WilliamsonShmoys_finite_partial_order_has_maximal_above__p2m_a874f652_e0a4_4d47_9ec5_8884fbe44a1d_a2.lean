-- Prove2me | solution 1 for WilliamsonShmoys.finite_partial_order_has_maximal_above__p2m_a874f652_e0a4_4d47_9ec5_8884fbe44a1d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:08:52.74185+00:00
-- url     : https://prove2.me/submissions/5f3c0a36-070a-4e7d-9908-2613bab33594

import Mathlib

theorem solution {α : Type} [Finite α] [PartialOrder α] (P : α → Prop) (a : α)
    (ha : P a) : ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, P c → b ≤ c → c ≤ b := by
  simpa [Maximal] using (Finite.exists_le_maximal (p := P) ha)