-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_connected__p2m_bd57f3c8_e371_4c77_9b1f_383221a33d80_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:16:21.590946+00:00
-- url     : https://prove2.me/submissions/9ab2140d-e07a-4ebb-abd3-856f5da65b06

import Theorems.Thm_WilliamsonShmoys_drawing_to_euler_face_certificate__p2m_e2583d82_96a1_4ed4_8709_65222159201c_a5
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K) :
    letI : (L : SimpleGraph V) -> DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    K.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  letI : (L : SimpleGraph V) -> DecidableRel L.Adj :=
    fun L => Classical.decRel L.Adj
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.drawing_to_euler_face_certificate__p2m_e2583d82_96a1_4ed4_8709_65222159201c_a5
      K hcard hconn hK
  omega