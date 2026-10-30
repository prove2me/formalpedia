-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_triangulation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:37:26.116514+00:00
-- url     : https://prove2.me/submissions/2afe6ad0-1b63-4172-acf6-40a74ba67a70

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_drawable_supergraph_for_triangulation_extension
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_for_triangulation_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hYdraw : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V, Y ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      Z.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨Z, hYZ, hZdraw, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_drawable_supergraph_for_triangulation_extension
      Y hYdraw
  have hcount :=
    WilliamsonShmoys.maximal_drawable_edge_count_for_triangulation_extension
      Z hCard hZdraw hmax
  exact ⟨Z, hYZ, hZdraw, hcount⟩
