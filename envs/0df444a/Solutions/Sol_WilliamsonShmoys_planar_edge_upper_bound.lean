-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:34:00.758844+00:00
-- url     : https://prove2.me/submissions/ec6eec9f-36d8-41ce-8fd1-e7098e726356
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_upper_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hLH, hConnected, hDrawing, hEdgeCount⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension L hL hV
  exact hEdgeCount.trans
    (WilliamsonShmoys.planar_connected_edge_upper_bound H hConnected hDrawing hV)
