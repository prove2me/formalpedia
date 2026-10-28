-- Prove2me | solution 1 for WilliamsonShmoys.planar_single_edge_augmentation_c61b3391
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:09:24.545667+00:00
-- url     : https://prove2.me/submissions/41a01311-f2e7-46a8-bcac-4b66703f51c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_below_complete_has_nonadjacent_pair
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_nonadjacent_edge

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hE : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        H.edgeSet.ncard = G.edgeSet.ncard + 1 := by
  obtain ⟨u, v, huv, hnot⟩ :=
    WilliamsonShmoys.planar_edge_count_below_complete_has_nonadjacent_pair G hV hE
  exact WilliamsonShmoys.planar_drawing_add_nonadjacent_edge G hG u v huv hnot