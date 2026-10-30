-- Prove2me | solution 1 for WilliamsonShmoys.finite_partial_order_maximal_above__p2m_c73a1eef_abb4_46aa_80da_3fb553ccc4a8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:55:12.133702+00:00
-- url     : https://prove2.me/submissions/02bef863-aa52-4fba-bde5-292693f3546e

import Mathlib
set_option autoImplicit false

theorem solution {α : Type} [Finite α] [PartialOrder α]
    (Q : α → Prop) (a : α) (ha : Q a) :
    ∃ b : α, a ≤ b ∧ Q b ∧ ∀ c : α, b ≤ c → Q c → c = b := by
  obtain ⟨b, hab, hb⟩ := Finite.exists_le_maximal (p := Q) ha
  refine ⟨b, hab, hb.1, ?_⟩
  intro c hbc hc
  exact le_antisymm (hb.2 hc hbc) hbc