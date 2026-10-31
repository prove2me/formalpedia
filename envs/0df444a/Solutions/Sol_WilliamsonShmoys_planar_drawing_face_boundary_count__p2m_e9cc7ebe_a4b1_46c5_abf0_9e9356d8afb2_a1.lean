-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_boundary_count__p2m_e9cc7ebe_a4b1_46c5_abf0_9e9356d8afb2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:16:13.045485+00:00
-- url     : https://prove2.me/submissions/78fb01d1-b3cd-4bb7-9dce-894acfcd5ccc

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_simple_graph_edge_bound__p2m_6d9d7968_a23c_4a93_aa91_407e3c15a842_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V)
    {f : ℕ}
    (hEuler : Fintype.card V + f = G.edgeSet.ncard + 2) :
    3 * f ≤ 2 * G.edgeSet.ncard := by
  have hbound := WilliamsonShmoys.planar_drawing_simple_graph_edge_bound__p2m_6d9d7968_a23c_4a93_aa91_407e3c15a842_a1
    G hG hconn hCard
  omega