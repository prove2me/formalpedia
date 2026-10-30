-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_graph_upper_edge_bound__p2m_bd178c5a_f4a2_457a_a392_a201150e58c2_a7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:36:09.90165+00:00
-- url     : https://prove2.me/submissions/2a96b05a-1a36-4dfc-8053-a7590aef541f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound

set_option autoImplicit false

open SimpleGraph
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.connected_planar_edge_bound
  | (apply _root_.WilliamsonShmoys.connected_planar_edge_bound <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.connected_planar_edge_bound <;> assumption)
