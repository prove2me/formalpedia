-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:35:57.01715+00:00
-- url     : https://prove2.me/submissions/7d2e7ee0-1a50-4d9f-90b7-dd75da6f4564
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_finite_inclusion_maximal_drawable_supergraph
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_drawable_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        3 * Fintype.card V = H.edgeSet.ncard + 6 := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_finite_inclusion_maximal_drawable_supergraph G hG
  refine ⟨H, hGH, hH, ?_⟩
  exact WilliamsonShmoys.edge_count_of_maximal_drawable_supergraph H hV hH hmax