-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_extension_20261026_planar_edge_count_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:09:33.073142+00:00
-- url     : https://prove2.me/submissions/c3449963-81fd-47e1-a802-61f166fd11a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_of_connected
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_of_disconnected

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  by_cases hconn : G.Connected
  · exact WilliamsonShmoys.planar_edge_count_of_connected G hG hconn hV
  · exact WilliamsonShmoys.planar_edge_count_of_disconnected G hG hV hconn