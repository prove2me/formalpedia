-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_429266ef_2658_4bcb_86f5_df3246663c92_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:46:58.702501+00:00
-- url     : https://prove2.me/submissions/1994698d-3129-4708-933e-8ddd14bcb560

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper_bound__p2m_517acab8_1dff_430a_88ba_b65381dc6f37_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_517acab8_1dff_430a_88ba_b65381dc6f37_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hV : 3 ≤ Fintype.card V) :
    Z.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hZH, hHconn, hHplanar⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_517acab8_1dff_430a_88ba_b65381dc6f37_a1
      Z hZ hV
  have hHbound :=
    WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_517acab8_1dff_430a_88ba_b65381dc6f37_a1
      H hHconn hHplanar hV
  apply le_trans (Set.ncard_mono ?_) hHbound
  intro e he
  revert he
  refine e.ind ?_
  intro u v he
  rw [SimpleGraph.mem_edgeSet] at he ⊢
  exact hZH he
