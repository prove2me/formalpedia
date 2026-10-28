-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound_for_maximal_drawable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:33:43.150758+00:00
-- url     : https://prove2.me/submissions/4fb5b240-2d0f-4f02-92f8-60791a44f8bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_drawable_edge_bound
import Theorems.Thm_WilliamsonShmoys_connect_drawn_components

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hV : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hTH, hHDraw, hHConn⟩ :=
    WilliamsonShmoys.connect_drawn_components T hT hV
  have hEdges : T.edgeSet.ncard ≤ H.edgeSet.ncard :=
    Set.ncard_le_ncard hTH
  have hBound : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.connected_drawable_edge_bound H hHDraw hHConn hV
  omega