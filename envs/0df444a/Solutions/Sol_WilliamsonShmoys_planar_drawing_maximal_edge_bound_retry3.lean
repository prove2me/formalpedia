-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_edge_bound_retry3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:34:10.078789+00:00
-- url     : https://prove2.me/submissions/d614fcac-4470-4cab-a701-dd8aff568cb0

import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_bound_from_arcs

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  exact planar_drawingOn_edge_bound_from_arcs H hCard hDraw