-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_b9db41c8_79f8_4b68_86df_fe1252530a28_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:41:07.090912+00:00
-- url     : https://prove2.me/submissions/617c04b7-4557-4f73-b7aa-fbbe1d60c49f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_certificate__p2m_792d8105_156d_4ec7_b9fb_1feb01e02200_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hconn : H.Connected)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  classical
  change H.edgeFinset.card ≤ 3 * Fintype.card V - 6
  obtain ⟨f, heuler, hincidence⟩ :=
    WilliamsonShmoys.connected_planar_euler_face_certificate__p2m_792d8105_156d_4ec7_b9fb_1feb01e02200_a1
      H hconn hH hcard
  omega