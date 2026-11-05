-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph_supergraph_maximal__p2m_7fc18aad_d07a_49bb_b01c_abff1eddf2b3_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:18:44.322439+00:00
-- url     : https://prove2.me/submissions/72988200-49cb-464d-97ca-9969bfcdb4d9

import Mathlib

theorem solution {α : Type} [Finite α] [Preorder α] (x : α) (Q : α → Prop)
    (hx : Q x) :
    ∃ y : α, Q y ∧ x ≤ y ∧ ∀ z : α, Q z → y ≤ z → z ≤ y := by
  let p : α → Prop := fun y => Q y ∧ x ≤ y
  have hpx : p x := ⟨hx, le_rfl⟩
  obtain ⟨y, hxy, hymax⟩ :=
    (Finite.exists_le_maximal (α := α) (p := p) (a := x) hpx)
  rcases hymax with ⟨hpy, hymax'⟩
  refine ⟨y, hpy.1, hxy, ?_⟩
  intro z hQz hyz
  exact hymax' ⟨hQz, hxy.trans hyz⟩ hyz
