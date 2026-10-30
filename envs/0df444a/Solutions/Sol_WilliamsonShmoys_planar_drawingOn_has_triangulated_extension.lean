-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_has_triangulated_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:44:03.264143+00:00
-- url     : https://prove2.me/submissions/b18de22f-4f30-4150-a457-d796331c0cb3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_has_edge_maximal_extension
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_has_euler_edge_count
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawingOn_has_edge_maximal_extension H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.edge_maximal_planar_drawing_has_euler_edge_count K hK hmax hV⟩