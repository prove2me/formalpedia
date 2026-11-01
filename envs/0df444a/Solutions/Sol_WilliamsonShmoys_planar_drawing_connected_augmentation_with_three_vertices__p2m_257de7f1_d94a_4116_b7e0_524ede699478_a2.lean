-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation_with_three_vertices__p2m_257de7f1_d94a_4116_b7e0_524ede699478_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:58:31.449833+00:00
-- url     : https://prove2.me/submissions/cbd30654-92d9-4942-b62b-07afa25f3120
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_edge_superset__p2m_06aa9184_ad05_46a0_aba1_f0ef97c506a7_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected ∧
      M.edgeSet.ncard <= H.edgeSet.ncard := by
  obtain ⟨H, hHplanar, hHconn, hM_le_H⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph_edge_superset__p2m_06aa9184_ad05_46a0_aba1_f0ef97c506a7_a1
      M hplanar hcard
  refine ⟨H, hHplanar, hHconn, ?_⟩
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono hM_le_H)
