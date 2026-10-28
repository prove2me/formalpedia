-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T13:46:10.077199+00:00
-- url     : https://prove2.me/submissions/4e0d5220-e091-4c6b-8dce-6e569e2c53cc

import Mathlib

set_option autoImplicit false
theorem solution {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop) (a : α) (ha : P a) : ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c = b := by
  classical
  have hfin : ({J : α | a ≤ J ∧ P J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨a, le_rfl, ha⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩
