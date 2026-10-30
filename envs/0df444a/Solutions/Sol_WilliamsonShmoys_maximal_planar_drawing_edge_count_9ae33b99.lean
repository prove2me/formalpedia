-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_9ae33b99
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:47:59.734591+00:00
-- url     : https://prove2.me/submissions/b025c35f-271b-4b9e-8e61-fa78a32a21ce

import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hmax : WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K = H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hsub, hKplanar, hKcard⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulated_supergraph_edge_count
      H hmax.1 hCard
  have hKH : K = H := hmax.2 K hsub hKplanar
  simpa only [← hKH] using hKcard