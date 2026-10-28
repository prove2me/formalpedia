-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_same_vertex_set_d3f6855c
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:23:53.179627+00:00
-- url     : https://prove2.me/submissions/fdcd96d0-8eea-45b5-aaf2-3cd56c33bf0a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_same_vertex_set_for_target_957bde25
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_edge_count_for_target_957bde25

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    exists L : SimpleGraph V,
      K <= L /\
      L.edgeSet.ncard = 3 * Fintype.card V - 6 /\
      WilliamsonShmoys.HasPlanarDrawingOn L := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension_same_vertex_set_for_target_957bde25 K hK
  have hcount := WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count_for_target_957bde25 L hV hL hmax
  exact ⟨L, hKL, hcount, hL⟩