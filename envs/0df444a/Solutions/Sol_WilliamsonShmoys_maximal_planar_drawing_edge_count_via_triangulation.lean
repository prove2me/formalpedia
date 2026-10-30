-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_via_triangulation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:27:23.145389+00:00
-- url     : https://prove2.me/submissions/b1a52a87-efb3-4cb3-a068-1d0b9e9b8b46

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion_for_maximality

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hDrawL, hCountL⟩ :=
    WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion_for_maximality
      K hDraw hCard
  have hLK : L.edgeSet ⊆ K.edgeSet := hMax L hKL hDrawL
  have hEq : K.edgeSet = L.edgeSet := Set.Subset.antisymm hKL hLK
  simpa [hEq] using hCountL
