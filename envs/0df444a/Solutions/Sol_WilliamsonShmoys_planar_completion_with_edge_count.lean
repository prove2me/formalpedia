-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_with_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:41:21.320972+00:00
-- url     : https://prove2.me/submissions/5099e24f-6362-4064-b0e4-106cf9c1fc32
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_completion_choose_maximal_on_fixed_vertices
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_exact_euler_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_completion_choose_maximal_on_fixed_vertices H hV hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_drawable_graph_has_exact_euler_edge_count K hV hK hmax⟩