-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound_retry2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:26:03.794316+00:00
-- url     : https://prove2.me/submissions/216972dd-7894-4e2e-a3e4-dabd4cd79ffe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connectedification_retry2
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_retry2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hEdges, hConn, hHDraw⟩ :=
    WilliamsonShmoys.planar_drawing_connectedification_retry2 G hDraw
  have hHBound :=
    WilliamsonShmoys.connected_planar_edge_bound_retry2 H hHDraw hConn hCard
  omega