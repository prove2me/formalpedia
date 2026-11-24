-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_count_upper_from_drawing_20261027
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:48:09.126439+00:00
-- url     : https://prove2.me/submissions/5d0c933c-8370-4ed5-8470-ab9545333fe7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_aca21fa1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    (G.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 :=
  WilliamsonShmoys.planar_edge_count_upper_bound_aca21fa1 G hG hCard
