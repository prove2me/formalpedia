-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_875ae99f
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:48:44.753992+00:00
-- url     : https://prove2.me/submissions/40710a83-80ed-4b54-8798-17260cd4ea77
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_completion_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_edge_bound_1f6216d4_7176_426b_8eb5_1d4c84c6c67c

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKconn, hKdraw, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_connected_completion_1f6216d4_7176_426b_8eb5_1d4c84c6c67c H hdraw
  have hKbound :=
    WilliamsonShmoys.planar_drawing_connected_edge_bound_1f6216d4_7176_426b_8eb5_1d4c84c6c67c K hKdraw hKconn hV
  omega