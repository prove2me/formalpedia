-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_ba06bb4d_e92b_4537_887e_0721c652813c_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:03:45.334864+00:00
-- url     : https://prove2.me/submissions/2879f584-127d-4c9a-85c5-2d703e01ec10

import Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_face_count__p2m_94535f0f_7fcf_46ec_8860_fc174f378d1a_a1
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.connected_drawing_euler_face_count__p2m_94535f0f_7fcf_46ec_8860_fc174f378d1a_a1
      G hcard hconn hG
  omega