-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:23:14.809675+00:00
-- url     : https://prove2.me/submissions/caab0c74-1933-4fbe-9a53-7eb6ccc6fa0a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawingOn_edge_bound
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_bound_of_connected_case
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  apply WilliamsonShmoys.planar_drawingOn_edge_bound_of_connected_case K hK hV
  intro W _ _ G hG hconn hn
  exact WilliamsonShmoys.connected_planar_drawingOn_edge_bound G hG hconn hn