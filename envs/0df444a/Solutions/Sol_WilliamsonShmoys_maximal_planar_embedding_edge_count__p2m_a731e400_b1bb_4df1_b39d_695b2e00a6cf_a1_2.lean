-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_embedding_edge_count__p2m_a731e400_b1bb_4df1_b39d_695b2e00a6cf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:31:24.05492+00:00
-- url     : https://prove2.me/submissions/bfb9945e-c4aa-4a7b-9bd3-5b264e078d23

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hDraw : HasPlanarDrawingOn T) (hV : 3 <= Fintype.card V) (hMax : forall N : SimpleGraph V, T <= N -> HasPlanarDrawingOn N -> N <= T) : T.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4 T hDraw hV hMax
