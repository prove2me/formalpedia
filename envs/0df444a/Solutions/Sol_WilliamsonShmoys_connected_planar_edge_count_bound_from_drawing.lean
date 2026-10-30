-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_bound_from_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T21:56:33.372814+00:00
-- url     : https://prove2.me/submissions/13010728-aab1-4081-b55f-088d34a5efb9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_triangulation_extension

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConnected : G.Connected)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHPlanar, hEdges, hMaximalCount⟩ :=
    WilliamsonShmoys.connected_planar_drawing_triangulation_extension
      G hG hConnected hV
  omega