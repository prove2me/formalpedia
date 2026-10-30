-- Prove2me | solution 1 for WilliamsonShmoys.compact_locally_connected_subtype_has_arc__p2m_2a816385_c89c_4f86_af76_d62ca3e4e97f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:20:09.951989+00:00
-- url     : https://prove2.me/submissions/b6b5ba21-b8b9-487c-9f30-9a70dd585e25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_compact_locally_connected_metric_subtype_has_arc__p2m_e413f8c6_3436_44b7_927c_9061da113dbc_a1

set_option autoImplicit false

theorem solution {s : Set (ℝ × ℝ)} (hcompact : IsCompact s) (hpath : IsPathConnected s)
    (hlocal : LocallyConnectedSpace s) (a b : s) (hne : a ≠ b) :
    ∃ φ : ℝ → ℝ × ℝ, ContinuousOn φ (Set.Icc 0 1) ∧ Set.InjOn φ (Set.Icc 0 1) ∧
      φ 0 = a.val ∧ φ 1 = b.val ∧ (∀ t ∈ Set.Icc 0 1, φ t ∈ s) := by
  exact WilliamsonShmoys.compact_locally_connected_metric_subtype_has_arc__p2m_e413f8c6_3436_44b7_927c_9061da113dbc_a1
    (X := ℝ × ℝ) hcompact hpath hlocal a b hne