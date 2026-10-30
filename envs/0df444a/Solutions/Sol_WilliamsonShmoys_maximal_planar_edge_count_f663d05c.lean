-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_f663d05c
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:36:57.338404+00:00
-- url     : https://prove2.me/submissions/10270cb9-1d5b-493c-9c01-1169b56be5b3

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_f663d05c
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_f663d05c

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v⦄, L.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.maximal_planar_edge_count_upper_f663d05c L hL hV
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_f663d05c L hL hV hmax
  omega