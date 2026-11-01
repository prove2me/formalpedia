-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_mem_of_finite_poset__p2m_060318e6_9aa2_44ce_a8eb_f04f288fc5e7_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:43:53.366831+00:00
-- url     : https://prove2.me/submissions/ae97bfd0-1e7d-46ef-aad0-a2538fde4f26

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Fintype α] [PartialOrder α]
    (s : Finset α) (hs : s.Nonempty) :
    ∃ a ∈ s, ∀ b ∈ s, a ≤ b → b ≤ a := by
  obtain ⟨a, ha, hmax⟩ := s.exists_maximal hs
  refine ⟨a, ha, ?_⟩
  intro b hb hab
  exact hmax hb hab