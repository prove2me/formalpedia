-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_edge_maximal_planar_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:00:54.191379+00:00
-- url     : https://prove2.me/submissions/3c88137a-6d35-4b01-a853-8258f2537d2e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_for_maximal_drawing_32fad0ec
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_for_maximal_drawing_32fad0ec

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper : L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_edge_upper_bound_for_maximal_drawing_32fad0ec L hV hL
  have hlower : 3 * Fintype.card V - 6 ≤ L.edgeSet.ncard :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound_for_maximal_drawing_32fad0ec L hV hL hmax
  omega