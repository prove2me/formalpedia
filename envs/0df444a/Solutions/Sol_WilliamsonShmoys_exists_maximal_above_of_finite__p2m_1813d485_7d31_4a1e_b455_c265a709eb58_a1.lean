-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_above_of_finite__p2m_1813d485_7d31_4a1e_b455_c265a709eb58_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:20:49.49433+00:00
-- url     : https://prove2.me/submissions/427309a1-f3ab-4068-bfca-63f3f8b3d7c1

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop) (a : α) (ha : P a) :
    ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c ≤ b := by
  classical
  let s : Set α := {x | P x}
  have hs : s.Finite := Set.toFinite s
  have ha' : a ∈ s := ha
  obtain ⟨b, hab, hmax⟩ := hs.exists_le_maximal ha'
  refine ⟨b, hab, hmax.1, ?_⟩
  intro c hbc hc
  exact hmax.2 hc hbc