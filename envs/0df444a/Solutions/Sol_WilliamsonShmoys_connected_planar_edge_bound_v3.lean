-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound_v3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:12:27.729737+00:00
-- url     : https://prove2.me/submissions/556b0081-4784-46b7-9349-cb194e76c11d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_v3_triangulation_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hConn : H.Connected) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨K, hSub, hKDraw, hKCount, hEdges⟩ :=
    WilliamsonShmoys.connected_planar_edge_bound_v3_triangulation_extension
      H hV hDraw hConn
  omega