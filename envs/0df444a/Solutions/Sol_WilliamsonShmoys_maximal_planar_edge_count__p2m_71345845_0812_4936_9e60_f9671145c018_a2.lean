-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_71345845_0812_4936_9e60_f9671145c018_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:38:00.488181+00:00
-- url     : https://prove2.me/submissions/5ff95564-0ab5-4633-9403-2aef421c899c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_count__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U = T) :
    (letI : DecidableRel T.Adj := Classical.decRel T.Adj;
     3 * Fintype.card V = T.edgeFinset.card + 6) := by
  exact (WilliamsonShmoys.maximal_planar_euler_count__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2
    T hT hmax hV).symm