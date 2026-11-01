-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_f8136575_362d_4cf6_b5f8_07670116a17a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:21:08.628591+00:00
-- url     : https://prove2.me/submissions/e2b668ec-c298-4fba-8b35-2bf1e0d1d8ad

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_certificate__p2m_3061538d_e777_4f56_997f_0c12065c9e75_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler, hfaces⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_certificate__p2m_3061538d_e777_4f56_997f_0c12065c9e75_a1
      G hplanar hconn hcard
  have hbound : G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
    omega
  omega