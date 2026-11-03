-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_c996decd_a3a2_408a_aa7c_25c4f85a8988_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:56:32.83241+00:00
-- url     : https://prove2.me/submissions/bdc87fec-3c1e-4cb0-8f3f-85dc7c86700a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_exists_maximal__p2m_9bfbc735_ec6d_4d27_8e0c_d58af3810de3_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_9bfbc735_ec6d_4d27_8e0c_d58af3810de3_a1

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 = K.edgeSet.ncard := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_exists_maximal__p2m_9bfbc735_ec6d_4d27_8e0c_d58af3810de3_a1
      H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_9bfbc735_ec6d_4d27_8e0c_d58af3810de3_a1
      K hcard hK hmax⟩