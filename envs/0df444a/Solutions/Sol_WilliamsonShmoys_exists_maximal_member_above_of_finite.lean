-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_member_above_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:27.236848+00:00
-- url     : https://prove2.me/submissions/3836f565-1ac4-4462-87cc-12cb74880406

import Mathlib

set_option autoImplicit false
theorem solution
    {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop)
    (hdown : ∀ {a b : α}, a ≤ b → P b → P a)
    (a : α) (ha : P a) :
    ∃ b : α, a ≤ b ∧ P b ∧
      ∀ c : α, b ≤ c → P c → c = b := by
  have hfin : ({J : α | a ≤ J ∧ P J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨a, le_rfl, ha⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩
