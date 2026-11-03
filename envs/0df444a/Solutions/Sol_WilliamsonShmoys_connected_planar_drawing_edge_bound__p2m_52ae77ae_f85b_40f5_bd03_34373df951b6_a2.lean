-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:54:13.071679+00:00
-- url     : https://prove2.me/submissions/4ca4d546-c607-4cf7-91af-96af0689ee5b

import Theorems.Thm_WilliamsonShmoys_connected_drawing_face_count__p2m_044c324d_acb7_4615_b70a_8b8b8a044876_a2
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.connected_drawing_face_count__p2m_044c324d_acb7_4615_b70a_8b8b8a044876_a2
      H hH hconn hcard
  omega