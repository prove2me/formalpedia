-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_4685f39c435647d7b1342b986f94c2d5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:05:21.188893+00:00
-- url     : https://prove2.me/submissions/66124dda-a2ef-4755-a60f-2e0cef9829a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_4b22e7d2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_4b22e7d2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H →
      G.edgeSet ⊆ H.edgeSet →
      H.edgeSet ⊆ G.edgeSet) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper :=
    WilliamsonShmoys.planar_drawing_edge_upper_bound_4b22e7d2 G hV hG
  have hlower :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound_4b22e7d2 G hV hG hmax
  omega