-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion_on_same_vertices
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:09:37.563776+00:00
-- url     : https://prove2.me/submissions/fca7cb6f-2203-4d03-ad08-e61a87768cdc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_completion_20261026
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_for_completion_20261026
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKdraw, hKmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_completion_20261026 H hHdraw
  have hcount := WilliamsonShmoys.edge_count_of_maximal_planar_drawing_for_completion_20261026
    K hV hKdraw hKmax
  exact ⟨K, hHK, hKdraw, hcount⟩