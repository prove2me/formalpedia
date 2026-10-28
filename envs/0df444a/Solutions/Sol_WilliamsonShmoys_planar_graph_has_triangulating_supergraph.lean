-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulating_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:43:25.288046+00:00
-- url     : https://prove2.me/submissions/3868184d-0456-4872-8f0a-3a417d526227
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_search_maximal_planar_extension
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.finite_search_maximal_planar_extension K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.edge_maximal_planar_graph_edge_count L hV hL hmax⟩