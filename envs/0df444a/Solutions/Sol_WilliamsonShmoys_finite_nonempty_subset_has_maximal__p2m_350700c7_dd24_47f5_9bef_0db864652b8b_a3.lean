-- Prove2me | solution 1 for WilliamsonShmoys.finite_nonempty_subset_has_maximal__p2m_350700c7_dd24_47f5_9bef_0db864652b8b_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:39:13.18081+00:00
-- url     : https://prove2.me/submissions/a66f871b-3bcc-43c7-a71a-7a0fbca9db24

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Finite α] [PartialOrder α] (S : Set α) (hS : S.Nonempty) :
    ∃ a ∈ S, ∀ b ∈ S, a ≤ b → b = a := by
  obtain ⟨a, ha⟩ := S.toFinite.exists_maximal hS
  refine ⟨a, ha.1, ?_⟩
  intro b hb hab
  exact le_antisymm (ha.2 hb hab) hab