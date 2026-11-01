-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_completion__p2m_fc0abe73_fd21_4e9c_bb3c_f4df0112280b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:50:37.487162+00:00
-- url     : https://prove2.me/submissions/a3feab7d-026a-4fc5-9efb-b9abd294ccf4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_18dadb11_49a3_466e_95d7_24d3c5d5bdee_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_card__p2m_18dadb11_49a3_466e_95d7_24d3c5d5bdee_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
        K.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_18dadb11_49a3_466e_95d7_24d3c5d5bdee_a1
      H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_graph_edge_card__p2m_18dadb11_49a3_466e_95d7_24d3c5d5bdee_a1
      K hK hcard hmax⟩