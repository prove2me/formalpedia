-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_upper_bound_for_component_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:04:04.215532+00:00
-- url     : https://prove2.me/submissions/118a87eb-e08b-44fe-8663-954f9069a186

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound_add_six

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    3 ≤ Fintype.card V → G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  intro hcard
  have hbound :
      G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys_connected_planar_edge_count_bound_add_six
      G hG hconn hcard
  omega