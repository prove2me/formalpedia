-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_data__p2m_5d8e8105_9248_4e8a_84e6_9239becaa16b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:31:03.826975+00:00
-- url     : https://prove2.me/submissions/9c9e92a2-d5fb-4c72-9e18-b941dc7cbcb3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_1d9982e7_ae2e_41b5_99c8_f768b7d6d77d_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_1d9982e7_ae2e_41b5_99c8_f768b7d6d77d_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ F B : ℕ,
      Fintype.card V + F = K.edgeFinset.card + 2 ∧
      3 * F ≤ B ∧
      B = 2 * K.edgeFinset.card := by
  obtain ⟨F, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_count__p2m_1d9982e7_ae2e_41b5_99c8_f768b7d6d77d_a1
      K hK hconn
  have hEdge :=
    WilliamsonShmoys.planar_drawing_edge_bound__p2m_1d9982e7_ae2e_41b5_99c8_f768b7d6d77d_a1
      K hK hcard
  refine ⟨F, 2 * K.edgeFinset.card, hEuler, ?_, rfl⟩
  omega