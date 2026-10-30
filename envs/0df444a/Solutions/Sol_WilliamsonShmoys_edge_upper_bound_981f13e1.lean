-- Prove2me | solution 1 for WilliamsonShmoys.edge_upper_bound_981f13e1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:34:56.080983+00:00
-- url     : https://prove2.me/submissions/d907f435-c8f8-4414-9849-e80bb947685a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_upper_bound_connected
import Theorems.Thm_WilliamsonShmoys_edge_upper_bound_from_connected_case
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    (G.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by
  apply WilliamsonShmoys.edge_upper_bound_from_connected_case G hG hCard
  intro W instF instL H hConn hDraw hN
  exact WilliamsonShmoys.edge_upper_bound_connected H hConn hDraw hN