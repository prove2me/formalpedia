-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_mem_finset__p2m_5361ebef_f1bf_4ddf_9929_f0777c6d31bd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:52:45.611488+00:00
-- url     : https://prove2.me/submissions/7ed5fb38-a417-44cf-9a2c-00ecaec55464

import Mathlib
set_option autoImplicit false

theorem solution {α : Type} [Fintype α] [PartialOrder α]
    (S : Finset α) (hS : S.Nonempty) :
    ∃ a ∈ S, ∀ b ∈ S, a ≤ b → b ≤ a := by
  classical
  obtain ⟨a, ha⟩ := S.exists_maximal hS
  refine ⟨a, ha.1, ?_⟩
  intro b hb hab
  exact ha.2 hb hab