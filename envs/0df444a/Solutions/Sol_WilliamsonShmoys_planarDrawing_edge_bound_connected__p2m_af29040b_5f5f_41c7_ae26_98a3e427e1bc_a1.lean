-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_edge_bound_connected__p2m_af29040b_5f5f_41c7_ae26_98a3e427e1bc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:35:44.502632+00:00
-- url     : https://prove2.me/submissions/3a99bd54-572e-48dc-b7bd-eed2de1715a5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarDrawing_face_count_certificate__p2m_8700ddcb_5e54_440d_86e0_a8d22ebd60f0_a1
import Theorems.Thm_WilliamsonShmoys_planarDrawing_face_count_arithmetic__p2m_8700ddcb_5e54_440d_86e0_a8d22ebd60f0_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 6 ≤ 3 * Fintype.card V := by
  classical
  letI : DecidableRel G.Adj := dG
  obtain ⟨f, faceLength, hEuler, hTotalLength, hFaceLength⟩ :=
    WilliamsonShmoys.planarDrawing_face_count_certificate__p2m_8700ddcb_5e54_440d_86e0_a8d22ebd60f0_a1
      G dG hG hConn hcard
  exact WilliamsonShmoys.planarDrawing_face_count_arithmetic__p2m_8700ddcb_5e54_440d_86e0_a8d22ebd60f0_a1
    (Fintype.card V) f G.edgeFinset.card faceLength hEuler hTotalLength hFaceLength