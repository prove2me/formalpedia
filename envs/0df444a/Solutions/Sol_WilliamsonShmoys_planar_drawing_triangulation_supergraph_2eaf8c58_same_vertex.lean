-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:49:28.322893+00:00
-- url     : https://prove2.me/submissions/84078b1d-acc6-449c-b3b0-8f54d8f26e10
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_same_vertex_target

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.drawable_supergraph_maximal_extension M hM
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.maximal_drawable_graph_edge_count_same_vertex_target
      N hV hN hmax⟩