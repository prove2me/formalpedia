-- Prove2me | solution 1 for WilliamsonShmoys.simple_planar_edge_bound_any_components
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:02:34.621811+00:00
-- url     : https://prove2.me/submissions/afb018b8-2cd5-4dda-9788-8367e1a2f95c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound_connected
import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound_disconnected

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  by_cases hConn : L.Connected
  · exact WilliamsonShmoys.simple_planar_edge_bound_connected
      L hLdraw hCard hConn
  · exact WilliamsonShmoys.simple_planar_edge_bound_disconnected
      L hLdraw hCard hConn