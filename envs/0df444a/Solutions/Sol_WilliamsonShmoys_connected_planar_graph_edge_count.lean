-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_graph_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:17:48.401277+00:00
-- url     : https://prove2.me/submissions/ae0abd71-d4ad-40bd-adab-167b5c7b445e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_connected_planar_graph_euler_faces
import Theorems.Thm_WilliamsonShmoys_planar_graph_euler_face_incidence
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : Y.Connected)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    Y.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨F, hEuler⟩ :=
    WilliamsonShmoys.connected_planar_graph_euler_faces Y hconn hY
  have hIncidence :=
    WilliamsonShmoys.planar_graph_euler_face_incidence Y hV hconn hY F hEuler
  omega