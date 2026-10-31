-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_edge_bound__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T20:52:45.235002+00:00
-- url     : https://prove2.me/submissions/b98ae35e-27a1-4940-80b2-5f2fada97843

import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound_e51c1790

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) : M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_graph_edge_bound_e51c1790 M hV hDraw
