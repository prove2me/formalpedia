-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_on
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T21:48:51.578987+00:00
-- url     : https://prove2.me/submissions/7041dfdc-9879-464f-8b49-c5b0f824dd3a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_same_vertices
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound_from_drawing

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHConnected, hHPlanar, hEdgeCount⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension_same_vertices G hG hV
  have hConnectedBound :=
    WilliamsonShmoys.connected_planar_edge_count_bound_from_drawing
      H hHPlanar hHConnected hV
  omega