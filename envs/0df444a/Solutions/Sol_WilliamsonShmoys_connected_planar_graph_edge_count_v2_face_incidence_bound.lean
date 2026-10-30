-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_graph_edge_count_v2_face_incidence_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:34:34.548989+00:00
-- url     : https://prove2.me/submissions/de0e8d5f-9806-496f-ac12-a75ba5953535

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_connected_planar_graph_edge_count_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : Y.Connected)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (f : ℕ)
    (hEuler : Fintype.card V + f = Y.edgeSet.ncard + 2) :
    3 * f ≤ 2 * Y.edgeSet.ncard := by
  have hEdge := WilliamsonShmoys.connected_planar_graph_edge_count_bound
    Y hV hY
  omega