-- Prove2me | solution 1 for WilliamsonShmoys.compact_locally_connected_metric_subtype_has_arc__p2m_e413f8c6_3436_44b7_927c_9061da113dbc_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:31:26.511775+00:00
-- url     : https://prove2.me/submissions/eeaa5acd-2e22-4278-87b2-59047569fb93
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_compact_locally_connected_metric_subtype_has_local_arcs__p2m_de9ec37e_3877_485c_a882_6cad68becd14_a2
import Theorems.Thm_WilliamsonShmoys_local_arcs_and_path_connected_imply_arc__p2m_de9ec37e_3877_485c_a882_6cad68becd14_a2

set_option autoImplicit false

theorem solution {X : Type} [MetricSpace X] {s : Set X}
    (hcompact : IsCompact s) (hpath : IsPathConnected s)
    (hlocal : LocallyConnectedSpace s) (a b : s) (hne : a ≠ b) :
    ∃ φ : ℝ → X, ContinuousOn φ (Set.Icc 0 1) ∧
      Set.InjOn φ (Set.Icc 0 1) ∧ φ 0 = a.val ∧ φ 1 = b.val ∧
      (∀ t ∈ Set.Icc 0 1, φ t ∈ s) := by
  exact WilliamsonShmoys.local_arcs_and_path_connected_imply_arc__p2m_de9ec37e_3877_485c_a882_6cad68becd14_a2
    hpath
    (WilliamsonShmoys.compact_locally_connected_metric_subtype_has_local_arcs__p2m_de9ec37e_3877_485c_a882_6cad68becd14_a2
      hcompact hlocal)
    a b hne