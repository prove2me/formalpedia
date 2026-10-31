-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_3bbe118b_2c52_4e44_a40f_aa9dcfe8d0b0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:30:52.344867+00:00
-- url     : https://prove2.me/submissions/b423766e-f0a6-4936-9141-f5337019f473

import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_graph_6230202c_e2d1_4f54_a7eb_9eadc154ee57

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDraw : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.edge_count_of_maximal_planar_graph_6230202c_e2d1_4f54_a7eb_9eadc154ee57 M hDraw hCard hMax
