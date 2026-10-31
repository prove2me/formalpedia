-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound_of_connected_supergraph__p2m_a6e6652d_e481_443f_9c79_230fd6c973a0_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:21:33.207595+00:00
-- url     : https://prove2.me/submissions/3b7c57fc-516c-4582-810d-9ce870635a06

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_49b7695b_51be_40f3_8be0_b4fd9841a079_a1
import Theorems.Thm_WilliamsonShmoys_subgraph_edgeSet_ncard_le__p2m_49b7695b_51be_40f3_8be0_b4fd9841a079_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V)
    (hKH : K ≤ H)
    (hHconn : H.Connected)
    (hHplanar : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have hHedges := WilliamsonShmoys.connected_planar_edge_bound__p2m_49b7695b_51be_40f3_8be0_b4fd9841a079_a1
    H hHconn hHplanar hV
  have hKedges := WilliamsonShmoys.subgraph_edgeSet_ncard_le__p2m_49b7695b_51be_40f3_8be0_b4fd9841a079_a1
    K H hKH
  omega