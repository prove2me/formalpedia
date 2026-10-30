-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:46:29.399712+00:00
-- url     : https://prove2.me/submissions/fc5dc99d-700b-458f-b00d-866e657d3653

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_disconnected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  by_cases hconn : H.Connected
  · exact WilliamsonShmoys.planar_drawing_edge_count_connected H hV hH hconn
  · exact WilliamsonShmoys.planar_drawing_edge_count_disconnected H hV hH hconn