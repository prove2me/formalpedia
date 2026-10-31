-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_edge_bound__p2m_49b7695b_51be_40f3_8be0_b4fd9841a079_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:14:07.130486+00:00
-- url     : https://prove2.me/submissions/72eb167a-a45e-4c0f-8d9a-3cd197790e68

import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_from_embedding

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hplanar : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.connected_planar_drawing_edge_bound_from_embedding G hconn hplanar hV
