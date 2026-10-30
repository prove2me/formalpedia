-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound_20261028
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:19:21.726788+00:00
-- url     : https://prove2.me/submissions/3b8b2f46-cfc4-46be-b211-30b6db8d1f64

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_simpleGraph_edge_upper_bound_of_planar_drawing

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hMax : ∀ G : SimpleGraph V, H.edgeSet ⊆ G.edgeSet →
      HasPlanarDrawingOn G → G.edgeSet ⊆ H.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  exact WilliamsonShmoys.simpleGraph_edge_upper_bound_of_planar_drawing H hH hCard