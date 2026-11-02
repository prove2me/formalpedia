-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_of_connected_induced_bounds__p2m_74363dfc_5510_4e30_bbc0_84ec4a079719_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:51:08.799104+00:00
-- url     : https://prove2.me/submissions/3e86dbde-95db-4357-a4f8-6c2eb1b4d862

import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_connected_vertex_partition__p2m_7d0b953f_c62a_470f_b8ef_9a25b50c3ad5_a4
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_connected_vertex_partition__p2m_7d0b953f_c62a_470f_b8ef_9a25b50c3ad5_a4

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hlocal : ∀ (s : Finset V),
      (K.induce (↑s : Set V)).Connected →
      (letI : DecidableRel (K.induce (↑s : Set V)).Adj := Classical.decRel _;
       (K.induce (↑s : Set V)).edgeFinset.card ≤
         max 1 (3 * Fintype.card s - 6))) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     K.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  obtain ⟨parts, hparts⟩ :=
    WilliamsonShmoys.finite_connected_vertex_partition__p2m_7d0b953f_c62a_470f_b8ef_9a25b50c3ad5_a4 K
  exact WilliamsonShmoys.edge_bound_of_connected_vertex_partition__p2m_7d0b953f_c62a_470f_b8ef_9a25b50c3ad5_a4
    K hcard hlocal parts hparts