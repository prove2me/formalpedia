-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_maximal_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:11:32.309517+00:00
-- url     : https://prove2.me/submissions/43be81b0-a6d3-49a6-9ca4-5aca792bb3f3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_euler_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeSet ⊆ L.edgeSet →
      L.edgeSet ⊆ K.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hL, hKL, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_with_euler_edge_count K hK hV
  have hsets : K.edgeSet = L.edgeSet := Set.Subset.antisymm hKL (hmax L hL hKL)
  rw [hsets]
  exact hcount