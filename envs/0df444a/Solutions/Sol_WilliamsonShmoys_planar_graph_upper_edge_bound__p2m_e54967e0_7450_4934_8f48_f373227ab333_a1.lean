-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_upper_edge_bound__p2m_e54967e0_7450_4934_8f48_f373227ab333_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:25:50.970278+00:00
-- url     : https://prove2.me/submissions/5625e946-8056-4fea-a352-78499b6035de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_edge_ncard__p2m_bd178c5a_f4a2_457a_a392_a201150e58c2_a7
import Theorems.Thm_WilliamsonShmoys_connected_planar_graph_upper_edge_bound__p2m_bd178c5a_f4a2_457a_a392_a201150e58c2_a7

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hmono, hconn, hplanar⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph_edge_ncard__p2m_bd178c5a_f4a2_457a_a392_a201150e58c2_a7 L hL hV
  exact Nat.le_trans (Nat.add_le_add_right hmono 6)
    (WilliamsonShmoys.connected_planar_graph_upper_edge_bound__p2m_bd178c5a_f4a2_457a_a392_a201150e58c2_a7 H hplanar hconn hV)