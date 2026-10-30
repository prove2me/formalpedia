-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulated_extension_3fe8be02_4541_4d0a_bbf4_850e46d722fe
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:09:39.70242+00:00
-- url     : https://prove2.me/submissions/da56a98c-e2e8-49a1-b0b0-7743292113fd

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_dabb2cbe_7fe3_4213_96ba_204afbbd922b
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_dabb2cbe_7fe3_4213_96ba_204afbbd922b

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X) :
    ∃ Y : SimpleGraph V,
      X ≤ Y ∧
      WilliamsonShmoys.HasPlanarDrawingOn Y ∧
      3 * Fintype.card V = Y.edgeSet.ncard + 6 := by
  obtain ⟨Y, hXY, hY, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_dabb2cbe_7fe3_4213_96ba_204afbbd922b
      X hV hX
  exact ⟨Y, hXY, hY,
    WilliamsonShmoys.maximal_planar_graph_edge_count_dabb2cbe_7fe3_4213_96ba_204afbbd922b
      Y hV hY hmax⟩