-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:12:38.794723+00:00
-- url     : https://prove2.me/submissions/fa67b1dc-4f83-4eae-8ffd-32332b170242

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_planar_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_has_three_n_minus_six_edges

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_edge_maximal_planar_supergraph G hG
  exact ⟨K, hGK, hK,
    WilliamsonShmoys.maximal_planar_supergraph_has_three_n_minus_six_edges
      K hK hV hmax⟩