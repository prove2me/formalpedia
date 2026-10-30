-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_lower_bound_d974173a
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:49:55.386202+00:00
-- url     : https://prove2.me/submissions/7d6e7bf7-3251-42d9-98e4-710d32695bf3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulated_extension_d974173a

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hLdraw, hLcard⟩ :=
    WilliamsonShmoys.drawable_graph_has_triangulated_extension_d974173a K hdraw hV
  have hLK : L = K := hmax L hKL hLdraw
  rw [hLK] at hLcard
  omega