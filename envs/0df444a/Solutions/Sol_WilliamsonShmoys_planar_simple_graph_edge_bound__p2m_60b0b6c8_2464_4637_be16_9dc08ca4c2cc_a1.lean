-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_60b0b6c8_2464_4637_be16_9dc08ca4c2cc_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:35:39.471494+00:00
-- url     : https://prove2.me/submissions/91b21112-b56a-4ac2-831a-c6b402b08547
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data__p2m_ab4fcf06_6052_4762_83f6_1c588acec272_a1
import Theorems.Thm_WilliamsonShmoys_face_count_edge_bound__p2m_ab4fcf06_6052_4762_83f6_1c588acec272_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨F, instF, length, hsum, hlen, heuler⟩ :=
    WilliamsonShmoys.planar_drawing_face_data__p2m_ab4fcf06_6052_4762_83f6_1c588acec272_a1
      G hconn hG hV
  letI : Fintype F := instF
  exact WilliamsonShmoys.face_count_edge_bound__p2m_ab4fcf06_6052_4762_83f6_1c588acec272_a1
    (Fintype.card V) G.edgeSet.ncard F length hV hsum hlen heuler