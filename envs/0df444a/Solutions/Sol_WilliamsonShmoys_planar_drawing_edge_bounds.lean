-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:48:35.107068+00:00
-- url     : https://prove2.me/submissions/e62762f8-8f28-4064-8fa2-8ffdf5379a25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_edge_lower_bound
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_upper_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    Fintype.card V <= K.edgeSet.ncard + 1 ∧
      K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  constructor
  · exact WilliamsonShmoys.connected_edge_lower_bound K hconn
  · exact WilliamsonShmoys.connected_planar_drawing_edge_upper_bound K hV hK hconn
