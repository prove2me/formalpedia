-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_same_vertex_edge_completion_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:24:18.342784+00:00
-- url     : https://prove2.me/submissions/1d97aefa-6770-4990-9a0e-68397d021a4a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_for_completion_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_completion_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph_for_completion_bound H hH
  exact ⟨K, hHK,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_for_completion_bound K hV hK hmax⟩