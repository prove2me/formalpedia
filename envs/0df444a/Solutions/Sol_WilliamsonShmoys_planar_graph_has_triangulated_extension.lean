-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulated_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:13:56.221989+00:00
-- url     : https://prove2.me/submissions/90a3014d-867b-4a7f-b2f9-c8c0a6937405
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_extension_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_from_arcs

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKplanar, hKmax⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulated_extension_maximal_extension H hH hV
  have hCount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_from_arcs K hKplanar hKmax hV
  exact ⟨K, hHK, hKplanar, hCount⟩