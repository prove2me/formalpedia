-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_reaches_triangulation_bound_from_arc_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:21:13.110018+00:00
-- url     : https://prove2.me/submissions/e7ea9cd3-efbe-407e-979a-ac916c4a0b1f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_for_arc_drawing
import Theorems.Thm_WilliamsonShmoys_edge_maximal_arc_drawn_graph_has_triangulation_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L <= M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 <= M.edgeSet.ncard := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph_for_arc_drawing L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.edge_maximal_arc_drawn_graph_has_triangulation_bound
      M hV hM hmax⟩