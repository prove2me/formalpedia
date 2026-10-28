-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound_augmentation_1a9e3423_67b8_4196_8909_cc8d9eac42a0
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:39:04.376009+00:00
-- url     : https://prove2.me/submissions/19eda83b-1661-4f18-80f2-eb5a71623676
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_for_augmentation_2fefb580
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_bound_for_augmentation_2fefb580

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hGdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ U : SimpleGraph V,
      G ≤ U ∧ WilliamsonShmoys.HasPlanarDrawingOn U ∧
        3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by
  obtain ⟨U, hGU, hUdraw, hUmax⟩ :=
    WilliamsonShmoys.maximal_drawable_supergraph_for_augmentation_2fefb580 G hGdraw
  exact ⟨U, hGU, hUdraw,
    WilliamsonShmoys.maximal_drawable_edge_bound_for_augmentation_2fefb580
      U hUdraw hUmax hCard⟩