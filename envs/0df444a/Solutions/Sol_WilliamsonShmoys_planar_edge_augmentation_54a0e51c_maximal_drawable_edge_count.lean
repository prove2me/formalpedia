-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_54a0e51c_maximal_drawable_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:05:41.429778+00:00
-- url     : https://prove2.me/submissions/1e84d032-10de-4e69-89e3-973a6a693115

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_edge_count
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn H →
      H.edgeSet ⊆ G.edgeSet) :
    G.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, _, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_edge_count G hV hG
  have hHG : H.edgeSet ⊆ G.edgeSet := hmax H hGH hH
  have hedges : H.edgeSet = G.edgeSet := Set.Subset.antisymm hHG hGH
  simpa only [hedges] using hcount