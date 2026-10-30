-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulated_supergraph_77f664a0
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:57:06.779309+00:00
-- url     : https://prove2.me/submissions/f54ad8b7-ecef-4763-9925-2e05695a854f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_77f664a0
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_77f664a0

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V,
      (∀ u v, H.Adj u v → G.Adj u v) ∧
      HasPlanarDrawingOn G ∧
      G.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨G, hHG, hDrawG, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_77f664a0 H hDraw
  exact ⟨G, hHG, hDrawG,
    WilliamsonShmoys.maximal_planar_edge_count_77f664a0 G hCard hDrawG hmax⟩