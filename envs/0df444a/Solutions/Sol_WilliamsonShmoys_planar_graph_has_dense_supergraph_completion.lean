-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_dense_supergraph_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:34:08.915994+00:00
-- url     : https://prove2.me/submissions/ffce8a53-c9cd-431c-9644-b0b9f8636ce7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_reaches_triangulation_bound_from_arc_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawable_graph_edge_bound_from_arcs

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L <= M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hMlow⟩ :=
    WilliamsonShmoys.planar_supergraph_reaches_triangulation_bound_from_arc_drawing L hV hL
  have hMupper := WilliamsonShmoys.planar_drawable_graph_edge_bound_from_arcs M hV hM
  refine ⟨M, hLM, hM, ?_⟩
  omega