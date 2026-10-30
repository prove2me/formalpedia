-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:27:25.507153+00:00
-- url     : https://prove2.me/submissions/d0968b3b-68aa-4f1f-92bd-48e8e4e26bdf

import Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_extension_for_maximal_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : ∀ u v, Relation.ReflTransGen H.Adj u v)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by
  obtain ⟨K, hHK, hK, hKe⟩ :=
    WilliamsonShmoys.planar_graph_triangulation_extension_for_maximal_edge_bound H hH hV
  have hEq : K = H := hmax K hHK hK
  rw [hEq] at hKe
  exact le_of_eq hKe.symm