-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_for_edge_augmentation_7f31c9a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:54:13.34412+00:00
-- url     : https://prove2.me/submissions/7176e66a-775a-4bae-bfe0-b3bcd456faa1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_maximal_drawable_supergraph_7f31c9a2
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_maximal_drawable_edge_count_7f31c9a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hKH, hDrawH, hMax⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_maximal_drawable_supergraph_7f31c9a2 K hDraw
  exact ⟨H, hKH, hDrawH,
    WilliamsonShmoys.planar_triangulation_extension_maximal_drawable_edge_count_7f31c9a2 H hDrawH hCard hMax⟩