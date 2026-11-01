-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_above_finite_partial_order__p2m_867a30c3_e0cd_4780_a6e7_8570584f57fd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:43:00.496874+00:00
-- url     : https://prove2.me/submissions/3e342798-ab1b-461d-ad12-6dd04a54ee2c

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Finite α] [PartialOrder α] (P : α → Prop) (a : α) (ha : P a) : ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c ≤ b := by
  classical
  let S : Set α := {x | a ≤ x ∧ P x}
  have hS : S.Finite := Set.toFinite S
  have haS : a ∈ S := ⟨le_rfl, ha⟩
  obtain ⟨b, hab, hbmax⟩ := hS.exists_le_maximal haS
  have hbS : b ∈ S := hbmax.1
  change a ≤ b ∧ P b at hbS
  refine ⟨b, hab, hbS.2, ?_⟩
  intro c hbc hc
  exact hbmax.2 ⟨hab.trans hbc, hc⟩ hbc