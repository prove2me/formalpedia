-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_6fab6ec6_c4a2_4215_b61d_4e14bbc8fe70_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T10:35:47.011434+00:00
-- url     : https://prove2.me/submissions/6a9d3893-542c-4f39-850b-c303d06fd2f7

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_2a3bf938_54d7_4ba6_ba97_85998ae61b74_a4
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    ∃ (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj),
      HasPlanarDrawingOn Q ∧ Q.Connected ∧
        (letI : DecidableRel G.Adj := dG
         letI : DecidableRel Q.Adj := dQ
         G.edgeFinset ⊆ Q.edgeFinset) := by
  classical
  obtain ⟨Q, hQ, hsub, hconn⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_2a3bf938_54d7_4ba6_ba97_85998ae61b74_a4
      G hG hcard
  let dQ : DecidableRel Q.Adj := Classical.decRel _
  refine ⟨Q, dQ, hQ, hconn, ?_⟩
  letI : DecidableRel G.Adj := dG
  letI : DecidableRel Q.Adj := dQ
  exact SimpleGraph.edgeFinset_mono hsub
