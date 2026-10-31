-- Prove2me | solution 1 for WilliamsonShmoys.drawing_face_count_certificate__p2m_dbcd4af9_e055_47f7_910a_a01842a93823_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:07:59.792731+00:00
-- url     : https://prove2.me/submissions/37e8742c-6277-4a31-871c-977d06d8a72c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_euler_face_count__p2m_c50fd7db_db60_4155_a74b_9f8219c920fe_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_c50fd7db_db60_4155_a74b_9f8219c920fe_a1
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn H)
    (hConn : H.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f <= 2 * H.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_euler_face_count__p2m_c50fd7db_db60_4155_a74b_9f8219c920fe_a1
      H hPlanar hConn
  have hEdges :=
    WilliamsonShmoys.planar_edge_bound__p2m_c50fd7db_db60_4155_a74b_9f8219c920fe_a1
      H hPlanar hV
  refine ⟨f, hEuler, ?_⟩
  omega