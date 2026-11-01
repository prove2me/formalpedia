-- Prove2me | solution 1 for WilliamsonShmoys.finite_property_maximal_extension__p2m_1299aa4d_98c0_4add_b63d_d780039a027b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:58:53.940202+00:00
-- url     : https://prove2.me/submissions/c7559771-37f7-4dda-ac87-3d4c937ebe92

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop) (a : α) (ha : P a) :
    ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c = b := by
  classical
  let S : Set α := {b | a ≤ b ∧ P b}
  have hSfinite : S.Finite := Set.finite_univ.subset (by
    intro x hx
    simp)
  have haS : a ∈ S := ⟨le_rfl, ha⟩
  obtain ⟨b, hab, hmax⟩ := hSfinite.exists_le_maximal haS
  rcases hmax with ⟨hbS, hmax⟩
  refine ⟨b, hab, hbS.2, ?_⟩
  intro c hbc hc
  have hcb : c ≤ b := hmax ⟨hab.trans hbc, hc⟩ hbc
  exact (le_antisymm hbc hcb).symm