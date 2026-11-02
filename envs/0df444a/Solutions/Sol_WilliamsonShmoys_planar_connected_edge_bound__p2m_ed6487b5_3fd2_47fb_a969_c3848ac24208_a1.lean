-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_bound__p2m_ed6487b5_3fd2_47fb_a969_c3848ac24208_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:46:11.02798+00:00
-- url     : https://prove2.me/submissions/07cef6bb-02b6-4ec8-bf75-3b044577d333

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_bound__p2m_c26a86c1_c11b_4f85_a158_b9e12bec4015_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) (hcard : 3 <= Fintype.card V) :
    G.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hdec, hsub, hdraw, hle, hH⟩ :=
    WilliamsonShmoys.planar_completion_edge_bound__p2m_c26a86c1_c11b_4f85_a158_b9e12bec4015_a1
      G hG hconn hcard
  letI : DecidableRel H.Adj := hdec
  omega