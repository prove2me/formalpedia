-- Prove2me | solution 1 for WilliamsonShmoys.drawable_edge_count_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:14:20.502769+00:00
-- url     : https://prove2.me/submissions/d93dacec-8e65-44b0-ad13-f04ea147976c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_connected_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_drawable_connectivity_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    U.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨W, hUW, hmono, hWconn, hWdraw⟩ :=
    WilliamsonShmoys.drawable_connectivity_completion U hV hU
  have hbound :=
    WilliamsonShmoys.drawable_connected_edge_count_upper_bound W hV hWconn hWdraw
  omega