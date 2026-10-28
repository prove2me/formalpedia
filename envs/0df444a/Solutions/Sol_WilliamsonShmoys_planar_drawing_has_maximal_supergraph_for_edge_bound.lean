-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_supergraph_for_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:40:00.687697+00:00
-- url     : https://prove2.me/submissions/bf0a84dc-61d1-4337-9cc3-d6301e45bed9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_of_edgeSet_subset
import Theorems.Thm_WilliamsonShmoys_exists_maximal_edgeSet_superset

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet ⊆ H.edgeSet ∧
      ∀ L : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn L →
        H.edgeSet ⊆ L.edgeSet →
        L.edgeSet ⊆ H.edgeSet := by
  obtain ⟨H, hH, hKH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_edgeSet_superset
      (P := WilliamsonShmoys.HasPlanarDrawingOn)
      (fun G H hH hGH =>
        WilliamsonShmoys.hasPlanarDrawingOn_of_edgeSet_subset hH hGH)
      K hDrawing
  exact ⟨H, hH, hKH, fun L hL hHL => hmax L hL hHL⟩
