-- Prove2me | solution 1 for WilliamsonShmoys.finite_finset_maximal__p2m_d87be54e_bfcb_4aba_9277_804ad42ab6ab_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:31:43.114729+00:00
-- url     : https://prove2.me/submissions/33f10574-827a-4ece-b7c5-fc60521de2c2

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (s : Finset α) (hs : s.Nonempty) :
    ∃ a ∈ s, ∀ b ∈ s, a ≤ b → b ≤ a := by
  classical
  obtain ⟨a, ha⟩ := s.exists_maximal hs
  exact ⟨a, ha.1, fun b hb hab => ha.2 hb hab⟩