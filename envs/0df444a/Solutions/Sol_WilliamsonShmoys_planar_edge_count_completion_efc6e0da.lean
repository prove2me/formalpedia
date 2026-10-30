-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_completion_efc6e0da
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:56:33.286816+00:00
-- url     : https://prove2.me/submissions/babc09cd-fb07-44ba-bc71-28417ddec276

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal_finite
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_exact

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ J : SimpleGraph V,
      G ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨J, hGJ, hJ, hMax⟩ :=
    WilliamsonShmoys.drawable_supergraph_maximal_finite G hG
  refine ⟨J, hGJ, hJ, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count_exact J hV hJ hMax