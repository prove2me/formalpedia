-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_57594b84
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:46:22.830001+00:00
-- url     : https://prove2.me/submissions/7986c57c-b13c-4f8c-9ad5-914c0d64e6a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_extension_5685a8d2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_exact_5685a8d2

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
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨G, hSub, hGDraw, hGMaximal⟩ :=
    WilliamsonShmoys.planar_drawable_maximal_extension_5685a8d2 H hDraw
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count_exact_5685a8d2 G hGDraw hCard hGMaximal
  have hEq : G.edgeSet = H.edgeSet := hMaximal G hSub hGDraw
  rw [hEq] at hCount
  omega