-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_edge_count_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:40:43.417489+00:00
-- url     : https://prove2.me/submissions/0b1d4e7a-8187-4371-9d23-2f5f7cbb3103
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_augmentation_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_maximal_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ X : SimpleGraph V, W.edgeSet ⊆ X.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn X ∧
      3 * Fintype.card V ≤ X.edgeSet.ncard + 6 := by
  obtain ⟨X, hWX, hX, hmax⟩ :=
    WilliamsonShmoys.planar_augmentation_maximal_extension W hW
  exact ⟨X, hWX, hX,
    WilliamsonShmoys.planar_augmentation_maximal_edge_count X hV hX hmax⟩