-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_components_exact
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:35:58.208383+00:00
-- url     : https://prove2.me/submissions/f2648fb4-1355-41b9-9a47-9d954937d639
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_core_937ee64a84854eee
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_component_support_restrict_937ee64a84854eee
import Theorems.Thm_WilliamsonShmoys_connectedComponent_support_induce_connected_937ee64a84854eee
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_component_estimates_937ee64a84854eee

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hm : 2 ≤ L.edgeSet.ncard) :
    L.edgeSet.ncard + 3 * Nat.card L.ConnectedComponent + 3 ≤
      3 * Fintype.card V := by
  classical
  apply WilliamsonShmoys.planar_edge_bound_from_component_estimates_937ee64a84854eee L hV hm
  intro C inst hC
  letI : Fintype C.supp := inst
  exact WilliamsonShmoys.connected_planar_drawing_edge_bound_core_937ee64a84854eee
    (L.induce C.supp) hC
    (WilliamsonShmoys.connectedComponent_support_induce_connected_937ee64a84854eee L C)
    (WilliamsonShmoys.planarDrawingOn_component_support_restrict_937ee64a84854eee L hL C)