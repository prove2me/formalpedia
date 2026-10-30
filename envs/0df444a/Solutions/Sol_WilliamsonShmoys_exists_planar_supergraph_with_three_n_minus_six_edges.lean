-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_with_three_n_minus_six_edges
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:59:44.668622+00:00
-- url     : https://prove2.me/submissions/c97b9532-c94e-459f-add7-5b130933d728

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_three_n_minus_six_edges_target
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_three_n_minus_six_edges_target

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hLDraw, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_three_n_minus_six_edges_target K hDraw
  refine ⟨L, hKL, hLDraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count_for_three_n_minus_six_edges_target L hV hLDraw hMax