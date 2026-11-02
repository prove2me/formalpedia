-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_f2e67bcd_d844_4f8f_86df_68d56c93483a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:15:51.248183+00:00
-- url     : https://prove2.me/submissions/e4346981-4a49-48e2-96ae-100c49f16492
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_extension_to_edge_maximal__p2m_9aae8c1a_0088_4039_a6d9_b99fa0bd700a_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count__p2m_9aae8c1a_0088_4039_a6d9_b99fa0bd700a_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_extension_to_edge_maximal__p2m_9aae8c1a_0088_4039_a6d9_b99fa0bd700a_a1 M hM
  refine ⟨N, hMN, hN, ?_⟩
  exact WilliamsonShmoys.edge_maximal_planar_edge_count__p2m_9aae8c1a_0088_4039_a6d9_b99fa0bd700a_a1 N hN hcard hmax