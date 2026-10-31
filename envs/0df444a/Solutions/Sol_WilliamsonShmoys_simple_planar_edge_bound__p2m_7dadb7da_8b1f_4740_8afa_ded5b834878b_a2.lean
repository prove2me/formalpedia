-- Prove2me | solution 1 for WilliamsonShmoys.simple_planar_edge_bound__p2m_7dadb7da_8b1f_4740_8afa_ded5b834878b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:50:00.013643+00:00
-- url     : https://prove2.me/submissions/a5874fc7-4508-4033-88a2-e1d7e95728ed

import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound_e51c1790

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hCard : 3 <= Fintype.card V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : G.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_graph_edge_bound_e51c1790 G hCard hG
