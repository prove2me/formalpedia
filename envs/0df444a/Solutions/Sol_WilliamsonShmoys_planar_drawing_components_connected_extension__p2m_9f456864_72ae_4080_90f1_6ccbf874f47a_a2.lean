-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_components_connected_extension__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:44:08.157359+00:00
-- url     : https://prove2.me/submissions/f95c2536-980e-499f-bc22-32d0cd8941ff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_connected_extension_of_local_step__p2m_343e7634_bf89_4d0d_a54b_557d3af37c62_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_components__p2m_343e7634_bf89_4d0d_a54b_557d3af37c62_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      L ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  exact WilliamsonShmoys.finite_graph_connected_extension_of_local_step__p2m_343e7634_bf89_4d0d_a54b_557d3af37c62_a1
    WilliamsonShmoys.HasPlanarDrawingOn
    (fun G hG hDisconnected =>
      WilliamsonShmoys.planar_drawing_add_edge_between_components__p2m_343e7634_bf89_4d0d_a54b_557d3af37c62_a1
        G hG hDisconnected)
    L hL