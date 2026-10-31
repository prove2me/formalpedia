-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count__p2m_b94cb538_0af7_43ff_a8d3_ab44b482c981_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:22:27.694871+00:00
-- url     : https://prove2.me/submissions/3519f9e7-bb07-4011-b344-4a4402e35ae8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_equation__p2m_62a3a1a3_c41c_45ae_9d73_85a6165d1dd4_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_simple_edge_bound__p2m_62a3a1a3_c41c_45ae_9d73_85a6165d1dd4_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_equation__p2m_62a3a1a3_c41c_45ae_9d73_85a6165d1dd4_a1
      G hG hconn hCard
  have hBound :=
    WilliamsonShmoys.planar_drawing_simple_edge_bound__p2m_62a3a1a3_c41c_45ae_9d73_85a6165d1dd4_a1
      G hG hconn hCard
  refine ⟨f, hEuler, ?_⟩
  omega