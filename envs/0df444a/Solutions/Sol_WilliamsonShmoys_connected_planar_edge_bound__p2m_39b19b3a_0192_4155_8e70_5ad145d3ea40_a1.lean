-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_39b19b3a_0192_4155_8e70_5ad145d3ea40_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:38:20.342602+00:00
-- url     : https://prove2.me/submissions/c29da173-beb3-49ff-9d43-a7b98f77897b

import Theorems.Thm_WilliamsonShmoys_planar_drawing_simple_edge_bound_from_embedding

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hConn : G.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_simple_edge_bound_from_embedding G hCard hConn hDraw
