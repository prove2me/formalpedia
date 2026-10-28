-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_792d6233_0413_48c2_8c4d_fb4d15268d51
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:16:42.632702+00:00
-- url     : https://prove2.me/submissions/b037484a-1ae5-48d7-830b-a1c1d8b1fbb1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_count_extension_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hXdraw : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hMax : ∀ Y : SimpleGraph V, X ≤ Y →
      WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X) :
    3 * Fintype.card V = X.edgeSet.ncard + 6 := by
  obtain ⟨Y, hXY, hYdraw, hCount⟩ :=
    WilliamsonShmoys.planar_drawable_edge_count_extension_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2
      X hCard hXdraw
  have hYX : Y = X := hMax Y hXY hYdraw
  simpa [hYX] using hCount
