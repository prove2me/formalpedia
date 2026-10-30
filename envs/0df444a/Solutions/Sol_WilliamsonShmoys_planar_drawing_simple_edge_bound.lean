-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_simple_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:02:35.090697+00:00
-- url     : https://prove2.me/submissions/029216d9-a294-40a7-bfdf-30e91893f1a0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_edge_maximizer

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hDrawingH, hCard, hMax⟩ :=
    WilliamsonShmoys.exists_planar_edge_maximizer G hConnected hDrawing hV
  omega