-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion_b54e7d04
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:54:07.303649+00:00
-- url     : https://prove2.me/submissions/c511c5f6-d5e0-498a-a90b-a9ea1216e8a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_completion
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_graph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hGK, hK, hMax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_completion G hV hG
  have hMaxK : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet := by
    intro L hKL hL
    exact hMax L (Set.Subset.trans hGK hKL) hL
  exact ⟨K, hGK, hK,
    WilliamsonShmoys.edge_count_of_maximal_planar_graph K hV hK hMaxK⟩