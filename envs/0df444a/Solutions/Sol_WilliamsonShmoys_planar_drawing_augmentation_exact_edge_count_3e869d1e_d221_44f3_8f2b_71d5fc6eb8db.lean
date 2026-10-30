-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_augmentation_exact_edge_count_3e869d1e_d221_44f3_8f2b_71d5fc6eb8db
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:40:19.203057+00:00
-- url     : https://prove2.me/submissions/a17f95ba-503f-4f1f-bc93-509f73b19efa

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_exists_for_exact_edge_count
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_for_exact_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension_exists_for_exact_edge_count G hG
  refine ⟨K, hGK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_edge_count_for_exact_edge_count K hV hK hmax