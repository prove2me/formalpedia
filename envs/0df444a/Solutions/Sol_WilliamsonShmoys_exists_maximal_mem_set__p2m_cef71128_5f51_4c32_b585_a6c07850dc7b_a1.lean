-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_mem_set__p2m_cef71128_5f51_4c32_b585_a6c07850dc7b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:31:27.963273+00:00
-- url     : https://prove2.me/submissions/cd2f400f-4d46-4c56-b59c-4d27425feae4

import Mathlib

theorem solution {α : Type} [PartialOrder α] [Finite α] (S : Set α) (hS : S.Nonempty) :
    ∃ a, a ∈ S ∧ ∀ b, a ≤ b → b ∈ S → b = a := by
  obtain ⟨a, ha⟩ := (Set.toFinite S).exists_maximal hS
  refine ⟨a, ha.1, ?_⟩
  intro b hab hb
  exact le_antisymm (ha.2 hb hab) hab