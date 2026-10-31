-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_edge_bound__p2m_6fae641e_69bd_437f_8912_51466427af04_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:52:46.476001+00:00
-- url     : https://prove2.me/submissions/831f372a-fb43-415c-8375-7cff2b9cf513

import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound__p2m_346cbd2e_54dd_4cc1_8c07_090cbf4f0cd3_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hconn : G.Connected) (hG : HasPlanarDrawingOn G) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_simple_edge_bound__p2m_346cbd2e_54dd_4cc1_8c07_090cbf4f0cd3_a1 G hV hconn hG
