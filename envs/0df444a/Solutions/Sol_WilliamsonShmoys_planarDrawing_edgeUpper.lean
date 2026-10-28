-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_edgeUpper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:52:28.094461+00:00
-- url     : https://prove2.me/submissions/e8821abb-83cc-4105-982f-d411ba2ff351
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_connectedPlanarDrawing_edgeUpper
import Theorems.Thm_WilliamsonShmoys_planarDrawing_edgeUpper_of_connected_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  exact WilliamsonShmoys.planarDrawing_edgeUpper_of_connected_bound
    (fun H hconn hd hv => WilliamsonShmoys.connectedPlanarDrawing_edgeUpper H hconn hd hv)
    G hdraw hV