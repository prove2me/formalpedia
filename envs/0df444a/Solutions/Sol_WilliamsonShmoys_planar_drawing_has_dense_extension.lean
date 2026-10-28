-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_dense_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:11:47.682605+00:00
-- url     : https://prove2.me/submissions/ec316714-4d52-4c52-8ccb-afeabc87e1a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_finite_vertex_graph
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_edge_count_lower_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ W : SimpleGraph V, G.edgeSet ⊆ W.edgeSet ∧
      HasPlanarDrawingOn W ∧
      3 * Fintype.card V ≤ W.edgeSet.ncard + 6 := by
  obtain ⟨W, hGW, hW, hmax⟩ :=
    WilliamsonShmoys.maximal_drawable_extension_finite_vertex_graph G hG
  exact ⟨W, hGW, hW,
    WilliamsonShmoys.maximal_drawable_extension_edge_count_lower_bound W hV hW hmax⟩