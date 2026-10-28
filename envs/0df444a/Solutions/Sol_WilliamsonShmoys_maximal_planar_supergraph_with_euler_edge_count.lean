-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_with_euler_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:19:34.258169+00:00
-- url     : https://prove2.me/submissions/8e5c80a0-be77-43fe-9cb9-771c08cc267b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_maximum_edge_planar_supergraph
import Theorems.Thm_WilliamsonShmoys_maximum_edge_planar_graph_has_euler_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.exists_maximum_edge_planar_supergraph M hM
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.maximum_edge_planar_graph_has_euler_edge_count
      N hV hN hmax⟩
