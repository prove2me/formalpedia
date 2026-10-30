-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulated_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:24:54.861699+00:00
-- url     : https://prove2.me/submissions/a968df2a-bfdd-4749-a1eb-328ebf6b18e1

import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_by_finite_edges
import Theorems.Thm_WilliamsonShmoys_edge_count_of_inclusion_maximal_planar_drawing

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K)
    (n : Nat)
    (hLarge : 3 ≤ n)
    (hcard : Fintype.card V = n) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * n - 6 := by
  obtain ⟨L, hKL, hLdraw, hLmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_by_finite_edges K hDrawing
  exact ⟨L, hKL, hLdraw,
    WilliamsonShmoys.edge_count_of_inclusion_maximal_planar_drawing
      L hLdraw hLmax n hLarge hcard⟩