-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_supergraph_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:40:39.986061+00:00
-- url     : https://prove2.me/submissions/2b574ff9-c2e2-4a2a-9522-f32d60eb1b92
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_exists_drawable_edge_augmentation
import Theorems.Thm_WilliamsonShmoys_drawable_completion_from_augmentation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 = M.edgeSet.ncard := by
  exact WilliamsonShmoys.drawable_completion_from_augmentation
    L hV hL
    (fun M hM => WilliamsonShmoys.exists_drawable_edge_count_upper_bound M hV hM)
    (fun M _hLM hM hE =>
      WilliamsonShmoys.exists_drawable_edge_augmentation M hV hM hE)