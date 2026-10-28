-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_supergraph_1176f3f1_fbd8_4a0d_b66b_36bdd6543cc3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:56:19.523901+00:00
-- url     : https://prove2.me/submissions/95f8ab57-aad1-42c7-a570-60325969e76b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_on_fixed_vertex_type_4156f0d3
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_on_fixed_vertex_type_4156f0d3

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      Set.Subset G.edgeSet H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_on_fixed_vertex_type_4156f0d3 G hG
  exact ⟨H, hGH, hH,
    WilliamsonShmoys.maximal_drawable_graph_edge_count_on_fixed_vertex_type_4156f0d3 H hV hH hmax⟩