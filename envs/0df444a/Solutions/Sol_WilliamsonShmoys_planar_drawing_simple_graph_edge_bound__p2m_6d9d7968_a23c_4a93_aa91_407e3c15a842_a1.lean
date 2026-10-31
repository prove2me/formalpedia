-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_simple_graph_edge_bound__p2m_6d9d7968_a23c_4a93_aa91_407e3c15a842_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:28:17.906862+00:00
-- url     : https://prove2.me/submissions/628f9cd3-1c98-40bb-a6f3-6589835932cd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count__p2m_b94cb538_0af7_43ff_a8d3_ab44b482c981_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFace⟩ :=
    WilliamsonShmoys.planar_drawing_face_count__p2m_b94cb538_0af7_43ff_a8d3_ab44b482c981_a2
      G hG hconn hCard
  omega
