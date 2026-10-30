-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_c61b3391
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:09:35.339459+00:00
-- url     : https://prove2.me/submissions/e90c887a-95a0-4e61-a749-01aff39be289

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_connected_c61b3391
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_of_connected_case_c61b3391

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  apply WilliamsonShmoys.planar_edge_count_upper_bound_of_connected_case_c61b3391
      G hV hG
  intro W _ _ H hW hconn hdraw
  exact WilliamsonShmoys.planar_edge_count_upper_bound_connected_c61b3391
      H hW hconn hdraw