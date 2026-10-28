-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_above_in_finite_partial_order
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:17:46.912379+00:00
-- url     : https://prove2.me/submissions/590f7155-5334-491e-9df4-ce5ea34bbf29

import Mathlib
set_option autoImplicit false

theorem solution {α : Type} [Finite α] [PartialOrder α] (x : α) (P : α → Prop) (hx : P x) :
    ∃ y : α, x ≤ y ∧ P y ∧ ∀ z : α, y ≤ z → P z → y = z := by
  classical
  let s : Set α := {y | x ≤ y ∧ P y}
  have hs : s.Finite := Set.toFinite s
  have hxs : x ∈ s := ⟨le_rfl, hx⟩
  obtain ⟨y, hy, hymax⟩ := hs.exists_maximal ⟨x, hxs⟩
  refine ⟨y, hy.1, hy.2, ?_⟩
  intro z hyz hP
  have hz : z ∈ s := ⟨hy.1.trans hyz, hP⟩
  exact le_antisymm hyz (hymax hz hyz)