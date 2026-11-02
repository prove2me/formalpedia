-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_f0f39874_5ae5_48cf_ae7d_0d6801141c64_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:41:24.173954+00:00
-- url     : https://prove2.me/submissions/65ba5fc6-1eb1-4a1c-a838-e794d1e167ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_face_accounting__p2m_afce1f76_d895_40f4_a39d_a07d8ca5218a_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨F, hF, heuler, hfaces⟩ :=
    WilliamsonShmoys.connected_planar_drawing_face_accounting__p2m_afce1f76_d895_40f4_a39d_a07d8ca5218a_a3
      H hH hconn hcard
  letI : Fintype F := hF
  omega