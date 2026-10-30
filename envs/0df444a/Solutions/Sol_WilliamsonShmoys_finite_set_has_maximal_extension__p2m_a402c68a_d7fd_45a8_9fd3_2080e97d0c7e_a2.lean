-- Prove2me | solution 1 for WilliamsonShmoys.finite_set_has_maximal_extension__p2m_a402c68a_d7fd_45a8_9fd3_2080e97d0c7e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:29:36.257261+00:00
-- url     : https://prove2.me/submissions/ee4d7c32-7513-4a64-93c5-7a907e5db95a

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Preorder α] (S : Set α) (hS : S.Finite) (a : α)
    (ha : a ∈ S) : ∃ b, b ∈ S ∧ a ≤ b ∧ ∀ c, b ≤ c → c ∈ S → c ≤ b := by
  obtain ⟨b, hab, hbmax⟩ := hS.exists_le_maximal ha
  refine ⟨b, hbmax.1, hab, ?_⟩
  intro c hbc hc
  exact hbmax.2 hc hbc