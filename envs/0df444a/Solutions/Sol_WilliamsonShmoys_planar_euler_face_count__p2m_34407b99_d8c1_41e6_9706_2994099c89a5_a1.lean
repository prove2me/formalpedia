-- Prove2me | solution 1 for WilliamsonShmoys.planar_euler_face_count__p2m_34407b99_d8c1_41e6_9706_2994099c89a5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:56:40.193288+00:00
-- url     : https://prove2.me/submissions/d8c267b1-3ebd-4024-82e0-a3a93a4d3238

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_connected_edge_count_lower_bound__p2m_3e960d88_24fa_4e6d_b367_13e60076bdee_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by
  have hEdges :=
    WilliamsonShmoys.finite_connected_edge_count_lower_bound__p2m_3e960d88_24fa_4e6d_b367_13e60076bdee_a1
      G hconn
  refine ⟨G.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega