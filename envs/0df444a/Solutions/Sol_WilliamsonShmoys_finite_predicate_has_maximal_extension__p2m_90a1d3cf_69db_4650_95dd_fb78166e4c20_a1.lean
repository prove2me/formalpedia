-- Prove2me | solution 1 for WilliamsonShmoys.finite_predicate_has_maximal_extension__p2m_90a1d3cf_69db_4650_95dd_fb78166e4c20_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:07:25.431655+00:00
-- url     : https://prove2.me/submissions/1a9d0318-cfaa-4ca8-a1d6-d0a67c8749cf

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [PartialOrder α] [Finite α]
    (S : α → Prop) (a : α) (ha : S a) :
    ∃ b, S b ∧ ∀ c, b ≤ c → S c → c = b := by
  classical
  let T : Set α := {x | S x}
  have hT : T.Finite := Set.toFinite T
  have hTne : T.Nonempty := ⟨a, ha⟩
  obtain ⟨b, hb⟩ := hT.exists_maximal hTne
  refine ⟨b, hb.1, ?_⟩
  intro c hbc hc
  exact le_antisymm (hb.2 hc hbc) hbc