-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_edge_bound__p2m_4939bc54_bf93_4b2e_bbee_bc8378b5882a_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:36:27.642714+00:00
-- url     : https://prove2.me/submissions/7dfb0845-de79-4126-a192-7732482a0988

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_crossing_free_drawing_euler_face_certificate__p2m_81ed959b_71ee_4030_85d8_875841fa0344_a2
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 <= Fintype.card V) :
    H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.crossing_free_drawing_euler_face_certificate__p2m_81ed959b_71ee_4030_85d8_875841fa0344_a2
      H hH hconn hcard
  omega