-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_maximal_edge_bound__p2m_fc48bf70_67b7_4d76_9c36_25eeec7debc5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:47:08.376636+00:00
-- url     : https://prove2.me/submissions/5786ca91-6973-4a43-9b37-44c7e6bc75e4

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_66b1df0d_2f5a_4a83_9f88_9b13f7439798_a1

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  obtain ⟨M, hLM, hM, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_66b1df0d_2f5a_4a83_9f88_9b13f7439798_a1
      L hcard hL
  have hEq : M = L := hmax M hLM hM
  rw [hEq] at hcount
  exact le_of_eq hcount.symm