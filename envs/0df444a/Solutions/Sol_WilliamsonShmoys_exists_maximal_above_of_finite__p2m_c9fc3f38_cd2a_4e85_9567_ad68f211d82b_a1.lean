-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_above_of_finite__p2m_c9fc3f38_cd2a_4e85_9567_ad68f211d82b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:50:23.685055+00:00
-- url     : https://prove2.me/submissions/fc2950ac-c460-416c-8da5-cd75dab5c0fd

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [PartialOrder α] [Finite α] (x : α) (P : α → Prop)
    (hP : P x) : ∃ y, x ≤ y ∧ P y ∧ ∀ z, y ≤ z → P z → z = y := by
  obtain ⟨y, hxy, hy⟩ := Finite.exists_le_maximal (p := P) hP
  refine ⟨y, hxy, hy.1, ?_⟩
  intro z hyz hPz
  exact le_antisymm (hy.2 hPz hyz) hyz