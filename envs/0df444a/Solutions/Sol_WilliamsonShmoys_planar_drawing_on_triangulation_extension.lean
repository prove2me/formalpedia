-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_on_triangulation_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T21:12:30.590815+00:00
-- url     : https://prove2.me/submissions/20232f21-3854-47eb-bbee-ddb9b8330cf1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_for_triangulation_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_for_triangulation_extension

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension_for_triangulation_extension
      G hG hV
  have hcount :=
    WilliamsonShmoys.maximal_planar_graph_edge_count_for_triangulation_extension
      K hV hK hmax
  exact ⟨K, hGK, hK, hcount⟩