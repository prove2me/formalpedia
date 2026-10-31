-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_face_count_certificate__p2m_0a6cb8c8_85f4_4527_b550_0c59830e1a8e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T19:02:02.056674+00:00
-- url     : https://prove2.me/submissions/808590da-76eb-483d-98cd-8868b25f9136

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4
import Theorems.Thm_WilliamsonShmoys_face_boundary_list_bound__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected) :
    ∃ f : ℕ, f + Fintype.card V = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by
  obtain ⟨f, lengths, hEuler, hLength, hSum, hLower⟩ :=
    WilliamsonShmoys.connected_planar_face_boundary_decomposition__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4
      G hG hV hconn
  have hBound :=
    WilliamsonShmoys.face_boundary_list_bound__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4
      lengths hLower
  rw [hLength, hSum] at hBound
  exact ⟨f, hEuler, hBound⟩