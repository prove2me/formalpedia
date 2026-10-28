-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:06:57.673543+00:00
-- url     : https://prove2.me/submissions/a4de22b7-0dd7-4904-a1d7-a340a8b56f35
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hLower := WilliamsonShmoys.maximal_drawable_edge_count_lower
    M hM hMax hV
  have hUpper := WilliamsonShmoys.planar_drawing_edge_count_upper M hM hV
  omega