-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_of_strict_nat_measure__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T20:12:51.197145+00:00
-- url     : https://prove2.me/submissions/3c0f6f98-3973-4428-9c8d-63efa404a0ab

import Theorems.Thm_finite_poset_exists_maximal_member__p2m_2e3d33d0_6b5e_40a9_a786_4b1fab836e4e_a2

import Mathlib
set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (μ : α → ℕ)
    (hstrict : ∀ ⦃a b : α⦄, a ≤ b → a ≠ b → μ a < μ b)
    (hne : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b → b = a :=
  finite_poset_exists_maximal_member__p2m_2e3d33d0_6b5e_40a9_a786_4b1fab836e4e_a2 P hne