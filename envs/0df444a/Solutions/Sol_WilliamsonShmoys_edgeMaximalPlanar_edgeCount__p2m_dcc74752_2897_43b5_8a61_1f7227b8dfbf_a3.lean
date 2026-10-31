-- Prove2me | solution 1 for WilliamsonShmoys.edgeMaximalPlanar_edgeCount__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:52:31.427323+00:00
-- url     : https://prove2.me/submissions/8ef30b22-c7ca-4ca2-a72c-26525a254bab

import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_graph_edge_count_391f3239_9f51_4455_9b2f_cbbc61103aca

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hV : 3 <= Fintype.card V) (hDraw : HasPlanarDrawingOn N) (hMax : ∀ M : SimpleGraph V, N ≤ M → HasPlanarDrawingOn M → M = N) : N.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_maximal_graph_edge_count_391f3239_9f51_4455_9b2f_cbbc61103aca N hV hDraw hMax
