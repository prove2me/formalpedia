-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_a8cccb55
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:23:53.121996+00:00
-- url     : https://prove2.me/submissions/7084ffd4-509a-479e-8886-dddf787d826d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_a8cccb55
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_a8cccb55

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    W.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hWH, hconn, hdraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph_a8cccb55 W hV hW
  have hH := WilliamsonShmoys.connected_planar_edge_bound_a8cccb55 H hV hconn hdraw
  exact (Nat.add_le_add_right hWH 6).trans hH