-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_euler_face_incidence
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:40:51.54+00:00
-- url     : https://prove2.me/submissions/448d37a7-045a-4b76-a5dc-8b7da8f4b9bd

import Theorems.Thm_WilliamsonShmoys_planar_graph_euler_face_incidence_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : Y.Connected)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (F : Nat)
    (hEuler : Fintype.card V + F = Y.edgeSet.ncard + 2) :
    3 * F <= 2 * Y.edgeSet.ncard := by
  have hEdge := WilliamsonShmoys.planar_graph_euler_face_incidence_edge_bound Y hV hconn hY
  omega