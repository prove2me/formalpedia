-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_upper_bound__p2m_b041ba7e_9475_4324_b141_7c04552295c3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:44:20.275614+00:00
-- url     : https://prove2.me/submissions/d0f49f43-185a-4bc2-a438-61882e42b860
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_face_data__p2m_93e8e51b_b659_4e57_adae_24ec3eefdfaa_a2
import Theorems.Thm_WilliamsonShmoys_face_data_edge_bound__p2m_93e8e51b_b659_4e57_adae_24ec3eefdfaa_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨k, boundary, hEuler, hBoundarySum, hFaceLength⟩ :=
    WilliamsonShmoys.connected_planar_face_data__p2m_93e8e51b_b659_4e57_adae_24ec3eefdfaa_a2
      H hH hconn hV
  exact WilliamsonShmoys.face_data_edge_bound__p2m_93e8e51b_b659_4e57_adae_24ec3eefdfaa_a2
    (Fintype.card V) H.edgeSet.ncard k boundary hEuler hBoundarySum hFaceLength