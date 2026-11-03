-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_8555a31b_9435_47a6_94cc_80670b8cc7a7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:57:05.729204+00:00
-- url     : https://prove2.me/submissions/4c4571f7-93b6-497f-bf14-e8c9a931843a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_face_count_from_drawing__p2m_c59fe07e_0bca_4d4e_9b09_8335007f2f58_a2
import Theorems.Thm_WilliamsonShmoys_face_data_implies_edge_bound__p2m_c59fe07e_0bca_4d4e_9b09_8335007f2f58_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  apply WilliamsonShmoys_face_data_implies_edge_bound__p2m_c59fe07e_0bca_4d4e_9b09_8335007f2f58_a2 K hcard
  exact WilliamsonShmoys_planar_face_count_from_drawing__p2m_c59fe07e_0bca_4d4e_9b09_8335007f2f58_a2 K hcard hconn hK