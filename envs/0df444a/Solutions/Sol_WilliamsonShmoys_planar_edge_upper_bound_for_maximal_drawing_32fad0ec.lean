-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound_for_maximal_drawing_32fad0ec
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:09:44.562663+00:00
-- url     : https://prove2.me/submissions/a219ee88-8ff5-4c9b-b142-071b27743f21

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hsub, hconn, hdraw, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation L hV hL
  exact hcard.trans
    (WilliamsonShmoys.connected_planar_edge_upper_bound H hV hconn hdraw)
