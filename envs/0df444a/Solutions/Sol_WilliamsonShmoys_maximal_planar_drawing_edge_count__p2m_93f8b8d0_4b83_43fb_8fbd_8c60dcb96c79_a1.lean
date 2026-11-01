-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_93f8b8d0_4b83_43fb_8fbd_8c60dcb96c79_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:12:47.422453+00:00
-- url     : https://prove2.me/submissions/7f64b3b9-a3d8-4637-853b-3493578d171e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper__p2m_eaae8083_26da_4ee8_a632_1917071465a8_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_eaae8083_26da_4ee8_a632_1917071465a8_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    L.edgeFinset.card + 6 = 3 * Fintype.card V := by
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  have hupper := WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_eaae8083_26da_4ee8_a632_1917071465a8_a1 L hL hcard
  have hlower := WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_eaae8083_26da_4ee8_a632_1917071465a8_a1 L hL hmax hcard
  omega