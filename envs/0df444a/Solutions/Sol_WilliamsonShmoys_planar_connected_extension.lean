-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:37:59.453018+00:00
-- url     : https://prove2.me/submissions/8f899eeb-6fe8-4a41-b422-9affb63a37a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_one_edge_augmentation
import Theorems.Thm_WilliamsonShmoys_connected_extension_of_planar_augmentation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      N.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard := by
  apply WilliamsonShmoys.connected_extension_of_planar_augmentation M hV hM
  intro G hG hGdisc
  exact WilliamsonShmoys.planar_one_edge_augmentation G hG hGdisc