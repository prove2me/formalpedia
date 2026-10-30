-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:02:41.702181+00:00
-- url     : https://prove2.me/submissions/04b26d61-6f48-4ae2-8fc1-8385b9d57a69

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_57594b84
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_57594b84

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMaximal : ∀ G : SimpleGraph V,
      H.edgeSet ⊆ G.edgeSet →
      HasPlanarDrawingOn G →
      G.edgeSet = H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.planar_drawing_edge_count_upper_bound_57594b84 H hDraw hCard
  have hLower :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound_57594b84
      H hDraw hCard hMaximal
  omega
