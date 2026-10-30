-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_below_bound_for_edge_maximal_graph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:40:39.305429+00:00
-- url     : https://prove2.me/submissions/dc7fcc43-f379-493c-baa0-13c697227e02

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_augmentation
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_for_edge_augmentation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcount : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ M : SimpleGraph V,
      G.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      G.edgeSet.ncard < M.edgeSet.ncard := by
  obtain ⟨M, hGM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_augmentation G hG
  have hMcount :=
    WilliamsonShmoys.maximal_planar_graph_edge_count_for_edge_augmentation M hV hM hmax
  refine ⟨M, hGM, hM, ?_⟩
  rw [hMcount]
  exact hcount