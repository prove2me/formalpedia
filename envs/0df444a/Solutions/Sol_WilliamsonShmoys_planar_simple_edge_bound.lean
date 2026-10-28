-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:32:40.702904+00:00
-- url     : https://prove2.me/submissions/ec95b4ae-b199-4e68-ae18-a6c69b64c1cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_exists_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_of_maximal_extension

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hsub, hH, hmax, hcard⟩ :=
    WilliamsonShmoys.planar_simple_edge_bound_exists_maximal_extension G hG
  have hbound :=
    WilliamsonShmoys.planar_simple_edge_bound_of_maximal_extension H hH hV hmax
  omega