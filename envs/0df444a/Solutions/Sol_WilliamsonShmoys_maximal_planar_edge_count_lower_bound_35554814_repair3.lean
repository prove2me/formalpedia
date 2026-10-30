-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_35554814_repair3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:07:19.909417+00:00
-- url     : https://prove2.me/submissions/d2f2edb1-3f20-4dda-aa7b-583bf4a44d03

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_lower_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hMax : ∀ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q →
      Set.Subset P.edgeSet Q.edgeSet → Set.Subset Q.edgeSet P.edgeSet) :
    3 * Fintype.card V ≤ P.edgeSet.ncard + 6 := by
  obtain ⟨Q, hQ, hPQ, hbound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_count_lower_bound P hCard hP
  have hQP : Set.Subset Q.edgeSet P.edgeSet := hMax Q hQ hPQ
  have hcard : Q.edgeSet.ncard ≤ P.edgeSet.ncard := Set.ncard_mono hQP
  omega