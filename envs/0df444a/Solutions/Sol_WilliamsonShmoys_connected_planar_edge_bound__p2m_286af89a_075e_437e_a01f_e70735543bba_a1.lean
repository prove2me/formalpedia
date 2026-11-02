-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_286af89a_075e_437e_a01f_e70735543bba_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:31:15.635921+00:00
-- url     : https://prove2.me/submissions/81063338-7e2b-4521-add4-5ea4fbdbf5e2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_count__p2m_688f1835_390c_48d2_a756_3ce127433083_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.connected_planar_drawing_euler_face_count__p2m_688f1835_390c_48d2_a756_3ce127433083_a1
      H hcard hconn hH
  omega