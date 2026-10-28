-- Prove2me | solution 1 for WilliamsonShmoys.planar_one_edge_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:54:52.284992+00:00
-- url     : https://prove2.me/submissions/afbb6f2b-b6d3-4a8b-b824-e60de2a0b906
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_adds_missing_edge
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_lt_of_new_adj

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hdisc : ¬ M.Connected) :
    ∃ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet.ncard < N.edgeSet.ncard := by
  obtain ⟨N, hsub, hplanar, u, v, hnew, hmissing⟩ :=
    WilliamsonShmoys.planar_augmentation_adds_missing_edge M hM hdisc
  exact ⟨N, hsub, hplanar,
    WilliamsonShmoys.edgeSet_ncard_lt_of_new_adj M N hsub u v hnew hmissing⟩