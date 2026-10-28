-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:48:16.196281+00:00
-- url     : https://prove2.me/submissions/8c04268e-63ae-4606-9801-5c3f3f85fbe5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists_for_edge_bound
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_inclusion_maximal_drawing

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨H, hsub, hdraw, hmax⟩ :=
    WilliamsonShmoys.maximal_drawable_supergraph_exists_for_edge_bound G hG
  exact ⟨H, hsub, hdraw,
    WilliamsonShmoys.edge_bound_of_inclusion_maximal_drawing H hV hdraw hmax⟩