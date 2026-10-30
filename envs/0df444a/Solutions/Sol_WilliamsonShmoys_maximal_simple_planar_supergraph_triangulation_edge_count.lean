-- Prove2me | solution 1 for WilliamsonShmoys.maximal_simple_planar_supergraph_triangulation_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:03:04.76923+00:00
-- url     : https://prove2.me/submissions/5a88e74d-8fc4-40cc-9a26-6754f7c49b59

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hNK, hK, hKcard⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulation_extension N hN hV
  have hKN : K ≤ N := hMax K hNK hK
  have hEq : N = K := le_antisymm hNK hKN
  simpa [hEq] using hKcard