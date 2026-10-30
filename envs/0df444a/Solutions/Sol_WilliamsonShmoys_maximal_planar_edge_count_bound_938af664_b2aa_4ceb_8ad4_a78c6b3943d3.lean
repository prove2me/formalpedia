-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_bound_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:44:27.796915+00:00
-- url     : https://prove2.me/submissions/2f5c1f81-c972-448b-b2d7-ef58e579ad6a

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_from_drawing

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_edge_count_bound_from_drawing G hV hG