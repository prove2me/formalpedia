-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound__p2m_471d7036_f9f4_4c2e_9af1_ae12e523e288_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:14:25.374992+00:00
-- url     : https://prove2.me/submissions/3c51c574-cd2e-4557-9a5f-edcc06c7714e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data__p2m_5d8e8105_9248_4e8a_84e6_9239becaa16b_a1
import Theorems.Thm_WilliamsonShmoys_face_data_edge_bound__p2m_5d8e8105_9248_4e8a_84e6_9239becaa16b_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     K.edgeFinset.card + 6 <= 3 * Fintype.card V) := by
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  obtain ⟨F, B, hEuler, hBoundaryLower, hBoundaryCount⟩ :=
    WilliamsonShmoys.planar_drawing_face_data__p2m_5d8e8105_9248_4e8a_84e6_9239becaa16b_a1
      K hK hconn hcard
  exact WilliamsonShmoys.face_data_edge_bound__p2m_5d8e8105_9248_4e8a_84e6_9239becaa16b_a1
    K F B hEuler hBoundaryLower hBoundaryCount