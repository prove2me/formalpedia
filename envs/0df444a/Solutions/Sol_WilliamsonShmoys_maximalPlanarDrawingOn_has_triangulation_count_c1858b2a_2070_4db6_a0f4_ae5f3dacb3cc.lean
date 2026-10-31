-- Prove2me | solution 1 for WilliamsonShmoys.maximalPlanarDrawingOn_has_triangulation_count_c1858b2a_2070_4db6_a0f4_ae5f3dacb3cc
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:20:41.506959+00:00
-- url     : https://prove2.me/submissions/481fa21c-6faa-4f4e-a370-27d1c835f41b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edgeCount_le
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_addEdge_when_below_triangulation_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hMax : ∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S)
    (hCard : 3 ≤ Fintype.card V) :
    S.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planarDrawingOn_edgeCount_le S hS hCard
  by_contra hEq
  have hBelow : S.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
  obtain ⟨T, hST, hT⟩ :=
    WilliamsonShmoys.planarDrawingOn_addEdge_when_below_triangulation_count
      S hS hCard hBelow
  have hSame : T = S := hMax T (le_of_lt hST) hT
  subst T
  exact (lt_irrefl S) hST