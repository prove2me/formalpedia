-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_graph_edge_count_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:19:23.96838+00:00
-- url     : https://prove2.me/submissions/f54b8d9a-6b19-49d8-8464-bdbfa7135fa7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic
import Theorems.Thm_WilliamsonShmoys_connected_planar_graph_edge_count_v2_euler_face_witness
import Theorems.Thm_WilliamsonShmoys_connected_planar_graph_edge_count_v2_face_incidence_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : Y.Connected)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    Y.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.connected_planar_graph_edge_count_v2_euler_face_witness
      Y hconn hY
  have hIncidence :=
    WilliamsonShmoys.connected_planar_graph_edge_count_v2_face_incidence_bound
      Y hV hconn hY f hEuler
  omega
