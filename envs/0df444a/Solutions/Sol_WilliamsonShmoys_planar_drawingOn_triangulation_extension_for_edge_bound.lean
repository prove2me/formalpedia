-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_triangulation_extension_for_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:18:26.12062+00:00
-- url     : https://prove2.me/submissions/ce8f0af3-4fa9-447e-aee9-f244fbaacfd4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_extension_same_vertex_type
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_triangulation_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V, Q ≤ R ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      R.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨R, hQR, hR, hMax⟩ :=
    WilliamsonShmoys.planar_drawingOn_maximal_extension_same_vertex_type Q hQ
  exact ⟨R, hQR, hR,
    WilliamsonShmoys.maximal_planar_drawingOn_triangulation_edge_count R hCard hR hMax⟩