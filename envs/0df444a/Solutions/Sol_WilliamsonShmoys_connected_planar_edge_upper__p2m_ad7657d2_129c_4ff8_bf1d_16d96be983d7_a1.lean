-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_upper__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:08:03.366842+00:00
-- url     : https://prove2.me/submissions/cd6d8625-fd82-4e90-9fba-a0a6c34f861e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_certificate__p2m_b5c387cc_fe7e_4039_9011_ee95aed75dd4_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaceIncidence⟩ :=
    WilliamsonShmoys.connected_planar_euler_face_certificate__p2m_b5c387cc_fe7e_4039_9011_ee95aed75dd4_a2
      H hH hconn hcard
  omega
