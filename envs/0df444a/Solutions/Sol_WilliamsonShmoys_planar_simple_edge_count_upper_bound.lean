-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_count_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:59:24.113593+00:00
-- url     : https://prove2.me/submissions/ada7c8d9-3690-4844-8ad8-5d9ca1518eb1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_maximal_graph_bound
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_edgeSet_ncard_mono
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hMax⟩ :=
    WilliamsonShmoys.planar_simple_edge_bound_maximal_supergraph G hG
  have hBound :=
    WilliamsonShmoys.planar_simple_edge_bound_maximal_graph_bound H hV hH hMax
  have hEdges :=
    WilliamsonShmoys.planar_simple_edge_bound_edgeSet_ncard_mono G H hGH
  omega