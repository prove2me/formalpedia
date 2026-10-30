-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_supergraph_with_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:21:54.290219+00:00
-- url     : https://prove2.me/submissions/c585ad5f-30ed-464f-8f51-ab1e24fdee5e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_drawable_supergraph__p2m_b1fff909_3724_4412_b571_7f014957ce50_a3
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_edge_maximal_drawable__p2m_b1fff909_3724_4412_b571_7f014957ce50_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨K, hJK, hDrawK, hMax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_drawable_supergraph__p2m_b1fff909_3724_4412_b571_7f014957ce50_a3 J hDraw
  have hExact := WilliamsonShmoys.edge_bound_of_edge_maximal_drawable__p2m_b1fff909_3724_4412_b571_7f014957ce50_a3
    K hDrawK hCard hMax
  exact ⟨K, hJK, hDrawK, by omega⟩