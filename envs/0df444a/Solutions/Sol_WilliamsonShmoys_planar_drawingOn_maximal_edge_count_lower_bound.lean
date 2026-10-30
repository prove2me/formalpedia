-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_maximal_edge_count_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:57:10.650461+00:00
-- url     : https://prove2.me/submissions/bfc0ea2b-ff52-46b3-8e75-bfd7cd5c0ce0

import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_triangulation_extension_for_edge_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hMax : ∀ R : SimpleGraph V,
      Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q) :
    3 * Fintype.card V ≤ Q.edgeSet.ncard + 6 := by
  obtain ⟨R, hQR, hRPlanar, hEdges⟩ :=
    WilliamsonShmoys.planar_drawingOn_triangulation_extension_for_edge_bound Q hCard hQ
  have hRQ : R = Q := hMax R hQR hRPlanar
  subst R
  omega