-- Prove2me | solution 1 for WilliamsonShmoys.finite_preorder_has_maximal__p2m_7d28393b_3717_42d0_a7e1_00f1426861ad_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:12:18.36384+00:00
-- url     : https://prove2.me/submissions/f8d1ca83-9517-470d-a8f2-9da0214c0320

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {α : Type} [Fintype α] [Preorder α] (s : Finset α) (hne : s.Nonempty) :
    ∃ a : α, a ∈ s ∧ ∀ b : α, b ∈ s → a ≤ b → b ≤ a := by
  classical
  obtain ⟨a, ha, hmax⟩ := s.exists_maximalFor id hne
  exact ⟨a, ha, fun b hb hab => hmax hb hab⟩