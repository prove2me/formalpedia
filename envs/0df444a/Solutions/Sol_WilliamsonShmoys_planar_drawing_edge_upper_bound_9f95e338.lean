-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound_9f95e338
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:34:15.888713+00:00
-- url     : https://prove2.me/submissions/15f0072f-a845-4f6a-a631-3a5bcd9df011
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_disconnected

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn T) (hV : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  classical
  by_cases hconn : T.Connected
  · exact WilliamsonShmoys.planar_drawing_edge_bound_connected T hdraw hconn hV
  · exact WilliamsonShmoys.planar_drawing_edge_bound_disconnected T hdraw hconn hV