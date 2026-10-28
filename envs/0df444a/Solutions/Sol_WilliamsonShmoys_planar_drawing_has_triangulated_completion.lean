-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:09:41.602117+00:00
-- url     : https://prove2.me/submissions/6dc48b44-2a74-46b6-afd0-b1716ed30cd5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_completion
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_for_completion

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDrawing : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hKDrawing, hMaximal⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_completion H hDrawing
  have hCount := WilliamsonShmoys.maximal_planar_graph_edge_count_for_completion
    K hKDrawing hMaximal hV
  exact ⟨K, hHK, hKDrawing, hCount⟩
