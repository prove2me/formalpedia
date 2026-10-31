-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_finite_maximal__p2m_bed1e8e9_9063_4971_87d4_a573a94b3117_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:06:28.756838+00:00
-- url     : https://prove2.me/submissions/85e93fea-2241-4d6a-b447-71e333898a36

import Mathlib
set_option autoImplicit false

theorem solution {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop) (hP : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, x ≤ y → P y → y = x := by
  classical
  let s : Set α := {x | P x}
  have hs : s.Nonempty := by
    rcases hP with ⟨x, hx⟩
    exact ⟨x, hx⟩
  obtain ⟨x, hxmax⟩ := (Set.toFinite s).exists_maximal hs
  refine ⟨x, ?_, ?_⟩
  · simpa [s] using hxmax.1
  · intro y hxy hy
    have hyx : y ≤ x := hxmax.2 hy hxy
    exact le_antisymm hyx hxy