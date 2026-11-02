-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_a60c0160_4029_4185_bfe8_ff4b14f19470_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:20:13.148624+00:00
-- url     : https://prove2.me/submissions/c0c79ebd-f651-4b60-8c03-ffeb4504a582
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_planar_drawing_face_data__p2m_65b9f3b0_4e49_457f_8ae3_e5dab0f54711_a2
import Theorems.Thm_planar_face_length_sum_bound__p2m_65b9f3b0_4e49_457f_8ae3_e5dab0f54711_a2
import Theorems.Thm_planar_edge_bound_of_face_data__p2m_65b9f3b0_4e49_457f_8ae3_e5dab0f54711_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hconn : H.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : 3 ≤ Fintype.card V) :
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨f, length, heuler, hsum, hlen⟩ :=
    planar_drawing_face_data__p2m_65b9f3b0_4e49_457f_8ae3_e5dab0f54711_a2
      H hconn hdraw hn
  have hfaces :=
    planar_face_length_sum_bound__p2m_65b9f3b0_4e49_457f_8ae3_e5dab0f54711_a2
      f H.edgeFinset.card length hsum hlen
  exact
    planar_edge_bound_of_face_data__p2m_65b9f3b0_4e49_457f_8ae3_e5dab0f54711_a2
      (Fintype.card V) f H.edgeFinset.card hn heuler hfaces