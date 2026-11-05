-- Prove2me | solution 1 for WilliamsonShmoys.exists_rank_maximal_extension__p2m_15a542b2_5d3b_464a_bec6_5f7385b1f62b_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:41:58.018751+00:00
-- url     : https://prove2.me/submissions/c8dd7543-d282-407e-a1cd-ac6f44c56528

import Mathlib

set_option linter.unusedVariables false

theorem solution
    {α : Type} [Fintype α] [Preorder α]
    (P : α → Prop) (rank : α → Nat)
    (hstrict : ∀ a b, a ≤ b → a ≠ b → rank a < rank b)
    (a : α) (ha : P a) :
    ∃ b, P b ∧ a ≤ b ∧ ∀ c, P c → b ≤ c → c ≤ b := by
  let p : α → Prop := fun b => P b ∧ a ≤ b
  have hpa : p a := ⟨ha, le_rfl⟩
  obtain ⟨b, hab, hbmax⟩ :=
    (Finite.exists_le_maximal (α := α) (p := p) (a := a) hpa)
  rcases hbmax with ⟨hpb, hbmax'⟩
  refine ⟨b, hpb.1, hab, ?_⟩
  intro c hPc hbc
  exact hbmax' ⟨hPc, hab.trans hbc⟩ hbc
