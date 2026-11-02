-- Prove2me | solution 1 for WilliamsonShmoys.finite_predicate_maximal_extension__p2m_6802ab23_a3ac_43c6_8aa9_163dea1542b1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:41:11.51969+00:00
-- url     : https://prove2.me/submissions/7640ea59-52d6-427a-8711-a9038f9294ab

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (a : α) (ha : P a) :
    ∃ b, a ≤ b ∧ P b ∧ ∀ c, b ≤ c → P c → c = b := by
  classical
  obtain ⟨b, hab, hmax⟩ := Finite.exists_le_maximal ha
  refine ⟨b, hab, hmax.1, ?_⟩
  intro c hbc hPc
  exact le_antisymm (hmax.2 hPc hbc) hbc