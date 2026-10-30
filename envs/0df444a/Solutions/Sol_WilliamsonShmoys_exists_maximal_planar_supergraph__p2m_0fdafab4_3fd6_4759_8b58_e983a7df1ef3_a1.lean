-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_0fdafab4_3fd6_4759_8b58_e983a7df1ef3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T20:30:34.563099+00:00
-- url     : https://prove2.me/submissions/d12258b1-31c4-468f-a195-b6b7789b0806

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_edge_maximal_subgraph_above__p2m_8f0c4e79_82ed_4eab_8262_744ee1ed1865_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet ⊆ L.edgeSet := by
  classical
  exact exists_edge_maximal_subgraph_above__p2m_8f0c4e79_82ed_4eab_8262_744ee1ed1865_a1
    K WilliamsonShmoys.HasPlanarDrawingOn hK
    (by
      intro G H hHG hG
      rcases hG with ⟨p, arc, hp, hEdges, hDisjoint⟩
      refine ⟨p, arc, hp, ?_, ?_⟩
      · intro u v huv hAdj
        exact hEdges u v huv
          (G.mem_edgeSet.mp (hHG (H.mem_edgeSet.mpr hAdj)))
      · intro u v x y huv hxy hAdj₁ hAdj₂ hne t ht s hs heq
        exact hDisjoint u v x y huv hxy
          (G.mem_edgeSet.mp (hHG (H.mem_edgeSet.mpr hAdj₁)))
          (G.mem_edgeSet.mp (hHG (H.mem_edgeSet.mpr hAdj₂)))
          hne t ht s hs heq)