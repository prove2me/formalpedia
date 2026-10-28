-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bounds_41afc169_9eb4_4682_8d03_09ec36ef1b9a
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:03:42.040897+00:00
-- url     : https://prove2.me/submissions/8bdf0239-1a39-4dd1-a5c0-e8c49c3f4751
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_edge_lower_bound_planar_drawing_for_9a76f4a2_5658_436a_8a64_d2d1017687a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_for_9a76f4a2_5658_436a_8a64_d2d1017687a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : L.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    And (Fintype.card V - 1 <= L.edgeSet.ncard)
      (L.edgeSet.ncard <= 3 * Fintype.card V - 6) := by
  constructor
  case left =>
    exact WilliamsonShmoys.connected_edge_lower_bound_planar_drawing_for_9a76f4a2_5658_436a_8a64_d2d1017687a1 L hconn
  case right =>
    exact WilliamsonShmoys.planar_drawing_edge_upper_bound_for_9a76f4a2_5658_436a_8a64_d2d1017687a1 L hV hdraw