-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_edge_count__p2m_2313d792_5eb0_4345_85d6_32f091bb14d8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:12:58.550578+00:00
-- url     : https://prove2.me/submissions/963ce04e-a7c6-4822-aaa3-9c36744bdf13
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edge_count_upper__p2m_10767c1e_3761_455c_b81d_2c159386481f_a1
import Theorems.Thm_WilliamsonShmoys_maximalPlanarDrawingOn_edge_count_lower__p2m_10767c1e_3761_455c_b81d_2c159386481f_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planarDrawingOn_edge_count_upper__p2m_10767c1e_3761_455c_b81d_2c159386481f_a1 K hK hCard
  have hlower := WilliamsonShmoys.maximalPlanarDrawingOn_edge_count_lower__p2m_10767c1e_3761_455c_b81d_2c159386481f_a1 K hK hCard hmax
  omega