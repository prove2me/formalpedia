-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_triangulation_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:02:05.047486+00:00
-- url     : https://prove2.me/submissions/b4d145a5-8914-45f6-bcad-cef46a76cb36
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph G hG
  exact ⟨K, hGK, hK,
    WilliamsonShmoys.edge_maximal_planar_drawing_edge_count K hK hcard hmax⟩