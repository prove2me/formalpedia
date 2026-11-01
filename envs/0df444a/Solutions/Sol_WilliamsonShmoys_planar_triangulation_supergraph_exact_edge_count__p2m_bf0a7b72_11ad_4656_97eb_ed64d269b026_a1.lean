-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_bf0a7b72_11ad_4656_97eb_ed64d269b026_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:36:38.991602+00:00
-- url     : https://prove2.me/submissions/4ae53358-316d-4382-b28e-56bcbadc3f29
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_cb03d114_7f2d_468d_a111_d39943cc6a95_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_exact_edge_count__p2m_cb03d114_7f2d_468d_a111_d39943cc6a95_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  classical
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_cb03d114_7f2d_468d_a111_d39943cc6a95_a1
      M hV hM
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_cb03d114_7f2d_468d_a111_d39943cc6a95_a1
      N hV hN hmax⟩