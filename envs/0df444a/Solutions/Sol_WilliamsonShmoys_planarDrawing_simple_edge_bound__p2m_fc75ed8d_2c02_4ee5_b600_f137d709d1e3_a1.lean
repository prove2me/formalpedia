-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_simple_edge_bound__p2m_fc75ed8d_2c02_4ee5_b600_f137d709d1e3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:04:55.193207+00:00
-- url     : https://prove2.me/submissions/7cbe316f-f339-4f99-9705-748bbb144cd3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_certificate__p2m_4ec6bc0b_ec8a_4e25_875f_9ac5631f6eca_a2
import Theorems.Thm_WilliamsonShmoys_euler_face_count_implies_simple_edge_bound__p2m_4ec6bc0b_ec8a_4e25_875f_9ac5631f6eca_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 6 ≤
      3 * Fintype.card V := by
  classical
  letI : DecidableRel G.Adj := dG
  obtain ⟨f, length, hEuler, hIncidence, hLength⟩ :=
    WilliamsonShmoys.planar_drawing_face_count_certificate__p2m_4ec6bc0b_ec8a_4e25_875f_9ac5631f6eca_a2
      G dG hG hConn hcard
  exact WilliamsonShmoys.euler_face_count_implies_simple_edge_bound__p2m_4ec6bc0b_ec8a_4e25_875f_9ac5631f6eca_a2
    (Fintype.card V) f G.edgeFinset.card length hEuler hIncidence hLength