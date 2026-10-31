-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:33:38.503982+00:00
-- url     : https://prove2.me/submissions/cf5ad68b-77f7-4242-86f1-4ab58b6e28fb

import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_ws

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_graph_edge_count_ws M hM hV hMax
