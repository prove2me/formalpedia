-- Prove2me | solution 1 for WilliamsonShmoys.simple_planar_drawing_edge_bound__p2m_ae9acfb5_6e8a_4024_8144_fc4b457004a2_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:08:35.679049+00:00
-- url     : https://prove2.me/submissions/a7389bc7-78ce-49da-b717-323e4ad56bfd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_counts__p2m_376b67ec_1efe_4ea0_9e38_4777b8820599_a1
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_euler_face_counts__p2m_376b67ec_1efe_4ea0_9e38_4777b8820599_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_counts__p2m_376b67ec_1efe_4ea0_9e38_4777b8820599_a1
      H hH hconn hcard
  exact WilliamsonShmoys.edge_bound_of_euler_face_counts__p2m_376b67ec_1efe_4ea0_9e38_4777b8820599_a1
    (Fintype.card V) H.edgeFinset.card f heuler hfaces hcard