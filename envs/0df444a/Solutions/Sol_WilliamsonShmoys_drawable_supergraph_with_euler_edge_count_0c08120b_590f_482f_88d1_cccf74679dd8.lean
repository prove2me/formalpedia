-- Prove2me | solution 1 for WilliamsonShmoys.drawable_supergraph_with_euler_edge_count_0c08120b_590f_482f_88d1_cccf74679dd8
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:51:08.406716+00:00
-- url     : https://prove2.me/submissions/bbefa9d0-6fcb-4ec9-99c3-fcbc383593d3

import Mathlib
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal_extension_87a22553
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_euler_count_87a22553
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      X ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      X.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hsub, hHdraw, hcard, hmax⟩ :=
    WilliamsonShmoys.drawable_supergraph_maximal_extension_87a22553 X hdraw
  exact ⟨H, hsub, hHdraw, hcard,
    WilliamsonShmoys.maximal_drawable_euler_count_87a22553 H hHdraw hV hmax⟩
