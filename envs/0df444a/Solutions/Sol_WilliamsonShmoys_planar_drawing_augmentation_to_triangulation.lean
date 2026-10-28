-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_augmentation_to_triangulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:55:36.080992+00:00
-- url     : https://prove2.me/submissions/fd406bf2-4f41-4d13-9aac-ad9b159fa721
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_finite_maximal_planar_supergraph_136dc8a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_136dc8a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.exists_finite_maximal_planar_supergraph_136dc8a1 M hM
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.maximal_planar_edge_count_136dc8a1 N hV hN hmax⟩