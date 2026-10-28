-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:15:27.757571+00:00
-- url     : https://prove2.me/submissions/6242528a-cd3a-4c4d-b946-869260f85089

import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (a₀ : α) (ha₀ : P a₀) :
    ∃ a : α, a₀ ≤ a ∧ P a ∧ ∀ b : α, a ≤ b → P b → b ≤ a := by
  classical
  let s : Set α := {a | a₀ ≤ a ∧ P a}
  have hs_finite : s.Finite := Set.toFinite s
  have ha₀_mem : a₀ ∈ s := by
    simp [s, ha₀]
  obtain ⟨a, ha_max⟩ := hs_finite.exists_maximal ⟨a₀, ha₀_mem⟩
  refine ⟨a, ha_max.1.1, ha_max.1.2, ?_⟩
  intro b hab hPb
  have hb_mem : b ∈ s := ⟨ha_max.1.1.trans hab, hPb⟩
  exact ha_max.2 hb_mem hab