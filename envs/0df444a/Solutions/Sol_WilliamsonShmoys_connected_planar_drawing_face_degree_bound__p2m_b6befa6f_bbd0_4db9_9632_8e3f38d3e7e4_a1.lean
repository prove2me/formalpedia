-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_face_degree_bound__p2m_b6befa6f_bbd0_4db9_9632_8e3f38d3e7e4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:19:41.925085+00:00
-- url     : https://prove2.me/submissions/76ed00e1-4193-402a-af35-e461ee6d96ed

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_60b0b6c8_2464_4637_be16_9dc08ca4c2cc_a1
import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (f : ℕ) (hEuler : Fintype.card V + f = G.edgeSet.ncard + 2) :
    3 * f ≤ 2 * G.edgeSet.ncard := by
  have hE := WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_60b0b6c8_2464_4637_be16_9dc08ca4c2cc_a1 G hV hconn hG
  omega