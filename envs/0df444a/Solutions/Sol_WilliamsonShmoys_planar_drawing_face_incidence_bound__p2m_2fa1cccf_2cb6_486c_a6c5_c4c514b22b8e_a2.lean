-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_incidence_bound__p2m_2fa1cccf_2cb6_486c_a6c5_c4c514b22b8e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:03:16.563865+00:00
-- url     : https://prove2.me/submissions/137a666d-9092-4a61-945f-c94f04d23619

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_b3c9bfa4_c900_4902_b62c_e651fcb234b7_a1
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (faceCount : Nat)
    (hEuler : Fintype.card V + faceCount = G.edgeSet.ncard + 2) :
    3 * faceCount <= 2 * G.edgeSet.ncard := by
  have hEdge := WilliamsonShmoys.planar_drawing_edge_bound__p2m_b3c9bfa4_c900_4902_b62c_e651fcb234b7_a1
    G hcard hconn hG
  omega
