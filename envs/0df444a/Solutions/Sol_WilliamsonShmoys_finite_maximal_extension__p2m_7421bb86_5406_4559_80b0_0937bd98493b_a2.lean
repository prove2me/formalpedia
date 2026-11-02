-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_extension__p2m_7421bb86_5406_4559_80b0_0937bd98493b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:56:32.139286+00:00
-- url     : https://prove2.me/submissions/92208982-ef22-490d-aa29-7ef4769f8c93

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (x : α) (hx : P x) :
    ∃ y, x ≤ y ∧ P y ∧ ∀ z, y ≤ z → P z → z ≤ y := by
  classical
  let s : Finset α := Finset.univ.filter P
  have hxmem : x ∈ s := by
    simp [s, hx]
  obtain ⟨y, hxy, hymax⟩ := s.exists_le_maximal hxmem
  refine ⟨y, hxy, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hymax.1).2
  · intro z hyz hPz
    exact hymax.2 (by simp [s, hPz]) hyz