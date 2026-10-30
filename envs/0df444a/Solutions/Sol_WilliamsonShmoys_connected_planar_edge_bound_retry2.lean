-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound_retry2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:56:32.733718+00:00
-- url     : https://prove2.me/submissions/bb6d2ba7-5e00-40f4-9458-276c779cd716

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_retry2_triangulation_extension
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_retry2_edge_monotone

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hSub, _hDrawH, hCount⟩ :=
    WilliamsonShmoys.connected_planar_edge_bound_retry2_triangulation_extension
      G hDraw hConn hCard
  have hEdges :=
    WilliamsonShmoys.connected_planar_edge_bound_retry2_edge_monotone G H hSub
  omega