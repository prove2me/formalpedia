-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_drawing_edge_count__p2m_8d9b924c_10a8_4e46_9c92_7f3339daf0a6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:37:13.811412+00:00
-- url     : https://prove2.me/submissions/127892a2-2dfe-42c9-81fc-1fcf0c264eb3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_upper__p2m_2fe61b07_5675_43dd_a849_e69c0c6246fb_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_2fe61b07_5675_43dd_a849_e69c0c6246fb_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hMax : forall K : SimpleGraph V, N <= K -> HasPlanarDrawingOn K -> K = N) :
    letI : DecidableRel N.Adj := Classical.decRel N.Adj
    3 * Fintype.card V = N.edgeFinset.card + 6 := by
  have hU := WilliamsonShmoys.maximal_planar_drawing_edge_count_upper__p2m_2fe61b07_5675_43dd_a849_e69c0c6246fb_a1 N hV hN
  have hL := WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_2fe61b07_5675_43dd_a849_e69c0c6246fb_a1 N hV hN hMax
  omega