-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count_repair
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:21:47.394979+00:00
-- url     : https://prove2.me/submissions/7159e12e-4bfe-4955-8a4e-18e09c3c9dcd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_repair
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_repair

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V, L ≤ T ∧ HasPlanarDrawingOn T ∧
      3 * Fintype.card V = T.edgeSet.ncard + 6 := by
  obtain ⟨T, hLT, hT, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_repair L hL
  exact ⟨T, hLT, hT,
    WilliamsonShmoys.maximal_drawable_graph_edge_count_repair T hV hT hmax⟩