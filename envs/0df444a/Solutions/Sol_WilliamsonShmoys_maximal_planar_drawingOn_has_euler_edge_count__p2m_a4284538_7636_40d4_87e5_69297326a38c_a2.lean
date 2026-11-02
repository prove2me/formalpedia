-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_has_euler_edge_count__p2m_a4284538_7636_40d4_87e5_69297326a38c_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:52:41.114189+00:00
-- url     : https://prove2.me/submissions/960128e1-04e2-4ab7-969d-d2cfbb1c989a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_upper__p2m_c5a41056_5cba_4140_8251_f29430518514_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_lower__p2m_c5a41056_5cba_4140_8251_f29430518514_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hKDrawing : HasPlanarDrawingOn K)
    (hKMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    letI : ∀ L : SimpleGraph V, DecidableRel L.Adj := fun L => Classical.decRel L.Adj
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : ∀ L : SimpleGraph V, DecidableRel L.Adj := fun L => Classical.decRel L.Adj
  have hupper :=
    WilliamsonShmoys.maximal_planar_drawingOn_edge_count_upper__p2m_c5a41056_5cba_4140_8251_f29430518514_a1
      K hcard hKDrawing
  have hlower :=
    WilliamsonShmoys.maximal_planar_drawingOn_edge_count_lower__p2m_c5a41056_5cba_4140_8251_f29430518514_a1
      K hcard hKDrawing hKMax
  omega
