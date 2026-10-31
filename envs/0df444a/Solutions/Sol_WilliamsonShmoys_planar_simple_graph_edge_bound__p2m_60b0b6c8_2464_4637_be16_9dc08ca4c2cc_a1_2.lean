-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_60b0b6c8_2464_4637_be16_9dc08ca4c2cc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:00:00.463192+00:00
-- url     : https://prove2.me/submissions/735c2ed3-a9fa-4978-aec8-bcd27f1e706d

import Theorems.Thm_WilliamsonShmoys_planar_drawing_simple_edge_bound_from_embedding

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hconn : G.Connected) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_simple_edge_bound_from_embedding G hV hconn hG
