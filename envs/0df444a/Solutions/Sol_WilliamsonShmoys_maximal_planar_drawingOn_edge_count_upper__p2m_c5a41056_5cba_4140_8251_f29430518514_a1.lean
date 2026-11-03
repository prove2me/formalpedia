-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_edge_count_upper__p2m_c5a41056_5cba_4140_8251_f29430518514_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:57:56.66264+00:00
-- url     : https://prove2.me/submissions/5b3964f5-c250-4645-97bf-d8eb22186c37

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_401105e3_1529_4fdd_958a_7e12d53ff038_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hKDrawing : HasPlanarDrawingOn K) :
    letI : ∀ L : SimpleGraph V, DecidableRel L.Adj := fun L => Classical.decRel L.Adj
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  exact WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_401105e3_1529_4fdd_958a_7e12d53ff038_a1 K hcard hKDrawing