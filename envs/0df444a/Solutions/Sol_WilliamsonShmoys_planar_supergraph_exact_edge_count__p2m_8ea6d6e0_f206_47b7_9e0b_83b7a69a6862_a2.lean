-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_exact_edge_count__p2m_8ea6d6e0_f206_47b7_9e0b_83b7a69a6862_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:46:56.570206+00:00
-- url     : https://prove2.me/submissions/e25910a5-706f-497d-bf09-60e07b30d2ae

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_adb36ea0_1077_447f_b2c5_a4177e2cdb6e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_adb36ea0_1077_447f_b2c5_a4177e2cdb6e_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, HasPlanarDrawingOn K ∧
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
        3 * Fintype.card V = K.edgeFinset.card + 6) := by
  obtain ⟨K, hK, hHK, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal__p2m_adb36ea0_1077_447f_b2c5_a4177e2cdb6e_a1
      H hV hH
  refine ⟨K, hK, hHK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_adb36ea0_1077_447f_b2c5_a4177e2cdb6e_a1
    K hV hK hmax