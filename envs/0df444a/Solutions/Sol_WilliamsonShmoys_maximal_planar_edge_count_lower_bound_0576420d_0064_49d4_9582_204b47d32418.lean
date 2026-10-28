-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_0576420d_0064_49d4_9582_204b47d32418
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:20:53.954793+00:00
-- url     : https://prove2.me/submissions/c83e01c7-61b0-4a67-bc7b-6580c299d283
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_edge_count_supergraph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨T, hLT, hT, hEq⟩ :=
    WilliamsonShmoys.exists_planar_edge_count_supergraph L hL hCard
  have hEq' := hEq
  rw [hMax T hLT hT] at hEq'
  exact le_of_eq hEq'