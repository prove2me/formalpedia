-- Prove2me | solution 1 for WilliamsonShmoys.finite_poset_nonempty_subset_has_maximal__p2m_f1350172_eccd_4d30_8af3_b1246339198a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:49:21.965834+00:00
-- url     : https://prove2.me/submissions/cec2c1a4-82ca-4a91-9ac3-880e2e156c50

import Mathlib

set_option autoImplicit false

open Set

theorem solution
    {α : Type} [Finite α] [PartialOrder α]
    (Q : α → Prop) (hQ : ∃ a, Q a) :
    ∃ a, Q a ∧ ∀ b, a ≤ b → Q b → b ≤ a := by
  obtain ⟨a, ha⟩ := (Set.toFinite {a : α | Q a}).exists_maximal hQ
  refine ⟨a, ha.1, ?_⟩
  intro b hab hb
  exact ha.2 hb hab