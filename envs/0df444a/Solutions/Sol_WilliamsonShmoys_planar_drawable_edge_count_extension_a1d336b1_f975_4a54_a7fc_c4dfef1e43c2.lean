-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_edge_count_extension_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:44:03.221152+00:00
-- url     : https://prove2.me/submissions/6b34cc2f-5008-4005-ac7b-e830c0643cd6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal_extension_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hXdraw : WilliamsonShmoys.HasPlanarDrawingOn X) :
    exists Y : SimpleGraph V, X <= Y /\
      WilliamsonShmoys.HasPlanarDrawingOn Y /\
      3 * Fintype.card V = Y.edgeSet.ncard + 6 := by
  obtain ⟨Y, hXY, hYdraw, hMax⟩ :=
    WilliamsonShmoys.drawable_supergraph_maximal_extension_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2 X hXdraw
  exact ⟨Y, hXY, hYdraw,
    WilliamsonShmoys.maximal_drawable_edge_count_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2
      Y hCard hYdraw hMax⟩