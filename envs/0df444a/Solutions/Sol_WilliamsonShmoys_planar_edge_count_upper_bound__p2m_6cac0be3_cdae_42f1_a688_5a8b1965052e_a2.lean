-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_6cac0be3_cdae_42f1_a688_5a8b1965052e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:52:49.414385+00:00
-- url     : https://prove2.me/submissions/bc4d357a-9b8a-4291-a657-ba944f815f17

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawing_face_count_certificate__p2m_dbcd4af9_e055_47f7_910a_a01842a93823_a2
import Theorems.Thm_WilliamsonShmoys_face_count_arithmetic__p2m_dbcd4af9_e055_47f7_910a_a01842a93823_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn H)
    (hConn : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaceLength⟩ :=
    WilliamsonShmoys.drawing_face_count_certificate__p2m_dbcd4af9_e055_47f7_910a_a01842a93823_a2
      H hPlanar hConn hV
  exact WilliamsonShmoys.face_count_arithmetic__p2m_dbcd4af9_e055_47f7_910a_a01842a93823_a2
    (Fintype.card V) H.edgeSet.ncard f hEuler hFaceLength