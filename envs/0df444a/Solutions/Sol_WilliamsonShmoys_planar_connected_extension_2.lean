-- Prove2me | solution 2 for WilliamsonShmoys.planar_connected_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T04:36:46.146352+00:00
-- url     : https://prove2.me/submissions/963cdf3f-893b-4181-9b6c-062f3fdc7c93
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_extension_of_planar_augmentation
import Theorems.Thm_WilliamsonShmoys_planar_one_edge_augmentation__p2m_db324782_c561_499c_9a61_9d772f4e7760_a11

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      N.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard := by
  apply WilliamsonShmoys.connected_extension_of_planar_augmentation M hV hM
  intro G hG hGdisc
  exact WilliamsonShmoys.planar_one_edge_augmentation__p2m_db324782_c561_499c_9a61_9d772f4e7760_a11
    G hV hG hGdisc