-- Prove2me | solution 2 for WilliamsonShmoys.planar_single_edge_augmentation_c61b3391
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:59:26.38478+00:00
-- url     : https://prove2.me/submissions/512ba5ff-ad82-4d8f-8ef2-626c4e1fe97d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_edge_augmentation

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hE : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        H.edgeSet.ncard = G.edgeSet.ncard + 1 := by
  first
  | exact _root_.WilliamsonShmoys.exists_drawable_edge_augmentation
  | (apply _root_.WilliamsonShmoys.exists_drawable_edge_augmentation <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.exists_drawable_edge_augmentation <;> assumption)
