-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_triangulation_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:22:27.09055+00:00
-- url     : https://prove2.me/submissions/d5ebe2a8-6fcd-459b-966e-8fa52aedbb61
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_drawable_supergraph_for_extension
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation_edge_count_for_extension
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.drawable_graph_has_maximal_drawable_supergraph_for_extension K hK
  refine ⟨L, hKL, hL, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count_for_extension
    L hV hL hmax