-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_triangulation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:19:53.231777+00:00
-- url     : https://prove2.me/submissions/c8cdfe20-0dd3-4c75-887d-58af20d4adc2

import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_exists_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_from_drawing_cd0a3fa1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ G : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → G.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn G ∧
      G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨G, hHG, hG, hmax⟩ :=
    WilliamsonShmoys.planarDrawingOn_exists_maximal_extension H hH hV
  refine ⟨G, hHG, hG, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count_from_drawing_cd0a3fa1
    G hG hV hmax