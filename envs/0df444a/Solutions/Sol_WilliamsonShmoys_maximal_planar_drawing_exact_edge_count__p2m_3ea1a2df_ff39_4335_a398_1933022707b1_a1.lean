-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_3ea1a2df_ff39_4335_a398_1933022707b1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:46:02.431793+00:00
-- url     : https://prove2.me/submissions/d1a3cf43-d180-4eb4-bdda-c150854cc614

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_3ea1a2df_ff39_4335_a398_1933022707b1_a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card = 3 * Fintype.card V - 6) :=
  WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_3ea1a2df_ff39_4335_a398_1933022707b1_a2 M hcard hMdraw hMmax