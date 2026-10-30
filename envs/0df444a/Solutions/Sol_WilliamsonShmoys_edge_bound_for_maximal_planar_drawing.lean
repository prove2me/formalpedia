-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_for_maximal_planar_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:50:04.449189+00:00
-- url     : https://prove2.me/submissions/c03b594e-6865-4e03-b635-f925f47a5d18

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_bound_for_maximal_planar_drawing_core_a7343f26_3b41_4ce4_b028_9c7717c085a3

set_option autoImplicit false

open WilliamsonShmoys in

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax :
      ∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet.ncard <= H.edgeSet.ncard) :
    H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  exact WilliamsonShmoys.edge_bound_for_maximal_planar_drawing_core_a7343f26_3b41_4ce4_b028_9c7717c085a3 H hV hH