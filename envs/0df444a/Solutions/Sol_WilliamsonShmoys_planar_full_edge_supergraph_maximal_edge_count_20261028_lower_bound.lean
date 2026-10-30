-- Prove2me | solution 1 for WilliamsonShmoys.planar_full_edge_supergraph_maximal_edge_count_20261028_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:26:38.628517+00:00
-- url     : https://prove2.me/submissions/568d6621-60ec-4858-9c79-85d4667e6398

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_three_n_minus_six_edges

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet = K.edgeSet) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨L, hsub, hDrawL, hcard⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_with_three_n_minus_six_edges K hV hDraw
  have hEq : L.edgeSet = K.edgeSet := hmax L hsub hDrawL
  calc
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
      rw [hcard]
    _ = K.edgeSet.ncard := by rw [hEq]