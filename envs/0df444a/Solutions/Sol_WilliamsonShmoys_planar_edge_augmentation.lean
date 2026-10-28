-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:44:14.304649+00:00
-- url     : https://prove2.me/submissions/fe11a265-6cb3-4040-92d5-69c8a8cdb5e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_triangulation_extension
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_from_triangulation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hE : M.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = M.edgeSet.ncard + 1 := by
  apply WilliamsonShmoys.planar_edge_augmentation_from_triangulation M hV hM hE
  exact WilliamsonShmoys.planar_edge_augmentation_triangulation_extension M hV hM