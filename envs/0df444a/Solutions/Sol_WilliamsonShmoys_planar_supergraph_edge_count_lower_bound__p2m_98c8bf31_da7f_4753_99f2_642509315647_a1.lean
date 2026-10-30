-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_count_lower_bound__p2m_98c8bf31_da7f_4753_99f2_642509315647_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T18:53:34.65401+00:00
-- url     : https://prove2.me/submissions/49df45f9-fd3f-4b47-b529-724570a163ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_9cc0c9d9_a289_45c0_90c4_3b812fbd190b_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_9cc0c9d9_a289_45c0_90c4_3b812fbd190b_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      Set.Subset G.edgeSet M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨M, hsub, hdraw, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_9cc0c9d9_a289_45c0_90c4_3b812fbd190b_a1
      G hG
  exact ⟨M, hsub, hdraw,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_9cc0c9d9_a289_45c0_90c4_3b812fbd190b_a1
      M hV hdraw hmax⟩