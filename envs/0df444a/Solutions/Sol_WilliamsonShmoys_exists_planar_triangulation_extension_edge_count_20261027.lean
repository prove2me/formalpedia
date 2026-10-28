-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_extension_edge_count_20261027
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:01:26.797605+00:00
-- url     : https://prove2.me/submissions/c48edb48-ef6d-4162-b080-13f35e945379
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_20261027_job59ad8832
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_20261027_job59ad8832

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hGplanar : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨K, hsub, hdraw, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension_20261027_job59ad8832 G hGplanar
  exact ⟨K, hsub, hdraw,
    WilliamsonShmoys.maximal_planar_edge_count_20261027_job59ad8832
      K hV hdraw hmax⟩