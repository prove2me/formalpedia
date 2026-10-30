-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_planar_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:13:19.590401+00:00
-- url     : https://prove2.me/submissions/ee0e4bd2-668d-441f-b456-b55405f37f9d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_for_edge_bound
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_exact_edge_count_from_planarity

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hHmax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet → H.edgeSet ≠ K.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn K) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hsub, hKdraw, hKmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_for_edge_bound H hHdraw
  have hEq : H.edgeSet = K.edgeSet := by
    by_contra hne
    exact (hHmax K hsub hne) hKdraw
  have hExact :=
    WilliamsonShmoys.maximal_drawable_graph_has_exact_edge_count_from_planarity
      K hKdraw hCard hKmax
  rw [← hEq] at hExact
  omega