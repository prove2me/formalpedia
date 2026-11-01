-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_has_triangulation_edge_count__p2m_7f938502_4ebe_49de_af5d_b80801e1f743_a5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:29:02.04939+00:00
-- url     : https://prove2.me/submissions/b4f70902-8527-446f-b298-800680d7b883
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_exists_maximal_extension__p2m_c96f9502_b6a7_485d_895c_b4be9d2d28fa_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count__p2m_c96f9502_b6a7_485d_895c_b4be9d2d28fa_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
         K.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawingOn_exists_maximal_extension__p2m_c96f9502_b6a7_485d_895c_b4be9d2d28fa_a2
      H hH
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawingOn_edge_count__p2m_c96f9502_b6a7_485d_895c_b4be9d2d28fa_a2
      K hK hmax hcard
  exact ⟨K, hHK, hK, hcount⟩