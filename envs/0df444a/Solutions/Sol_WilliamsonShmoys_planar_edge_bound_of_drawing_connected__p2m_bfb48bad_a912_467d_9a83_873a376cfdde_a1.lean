-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_of_drawing_connected__p2m_bfb48bad_a912_467d_9a83_873a376cfdde_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:01:27.560647+00:00
-- url     : https://prove2.me/submissions/4946f0f3-a756-4d43-916e-c65d347c148c

import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_e9cc7ebe_a4b1_46c5_abf0_9e9356d8afb2_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_boundary_count__p2m_e9cc7ebe_a4b1_46c5_abf0_9e9356d8afb2_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_count__p2m_e9cc7ebe_a4b1_46c5_abf0_9e9356d8afb2_a1
      G hG hconn
  have hfaces :=
    WilliamsonShmoys.planar_drawing_face_boundary_count__p2m_e9cc7ebe_a4b1_46c5_abf0_9e9356d8afb2_a1
      G hG hconn hCard heuler
  omega