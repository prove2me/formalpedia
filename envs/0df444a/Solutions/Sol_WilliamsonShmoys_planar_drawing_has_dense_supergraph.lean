-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_dense_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:17:36.824885+00:00
-- url     : https://prove2.me/submissions/7410339d-48f9-4de3-9e9c-1d91ca8b2cc0

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_is_dense

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 <= K.edgeSet.ncard := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_edge_maximal_supergraph G hG
  exact ⟨K, hGK, hK,
    WilliamsonShmoys.edge_maximal_planar_drawing_is_dense K hK hV hmax⟩