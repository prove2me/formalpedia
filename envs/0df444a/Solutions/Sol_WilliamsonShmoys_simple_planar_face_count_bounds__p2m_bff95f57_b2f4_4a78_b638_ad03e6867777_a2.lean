-- Prove2me | solution 1 for WilliamsonShmoys.simple_planar_face_count_bounds__p2m_bff95f57_b2f4_4a78_b638_ad03e6867777_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:43:07.474652+00:00
-- url     : https://prove2.me/submissions/a041b8d6-1669-4719-b2c1-4bbd9cc1965c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_euler_face_count__p2m_34407b99_d8c1_41e6_9706_2994099c89a5_a1
import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound__p2m_34407b99_d8c1_41e6_9706_2994099c89a5_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_euler_face_count__p2m_34407b99_d8c1_41e6_9706_2994099c89a5_a1
      G hG hconn
  have hEdge :=
    WilliamsonShmoys.simple_planar_edge_bound__p2m_34407b99_d8c1_41e6_9706_2994099c89a5_a1
      G hG hconn hCard
  refine ⟨f, hEuler, ?_⟩
  omega