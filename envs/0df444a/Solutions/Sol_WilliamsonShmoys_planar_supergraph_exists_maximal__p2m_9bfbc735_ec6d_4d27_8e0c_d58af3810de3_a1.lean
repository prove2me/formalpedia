-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_exists_maximal__p2m_9bfbc735_ec6d_4d27_8e0c_d58af3810de3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:12:25.137412+00:00
-- url     : https://prove2.me/submissions/61ef86f7-2b32-4319-a0b3-7ca41f4d82be

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_finite_downward_property__p2m_dbde89e8_c849_4801_a07f_e697f1afc8ec_a1
import Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_subgraph__p2m_dbde89e8_c849_4801_a07f_e697f1afc8ec_a1

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by
  apply WilliamsonShmoys.exists_maximal_supergraph_for_finite_downward_property__p2m_dbde89e8_c849_4801_a07f_e697f1afc8ec_a1
    H WilliamsonShmoys.HasPlanarDrawingOn hH
  intro G G' hGG' hG'
  exact WilliamsonShmoys.hasPlanarDrawingOn_subgraph__p2m_dbde89e8_c849_4801_a07f_e697f1afc8ec_a1 hGG' hG'