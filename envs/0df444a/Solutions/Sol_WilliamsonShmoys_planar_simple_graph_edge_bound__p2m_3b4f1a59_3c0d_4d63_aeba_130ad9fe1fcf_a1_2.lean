-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_3b4f1a59_3c0d_4d63_aeba_130ad9fe1fcf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:10:47.720614+00:00
-- url     : https://prove2.me/submissions/27377707-498b-4564-8d6f-b2e2ad81e788

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_count_bound_retry3 G hDraw hV
