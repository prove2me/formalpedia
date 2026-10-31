-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangulation_completion__p2m_3bdd09ac_e2e3_4767_b598_2a6e24b78964_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:40:36.124326+00:00
-- url     : https://prove2.me/submissions/fe0fa025-f090-4c76-8e39-8eb7c95637ac

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_2c3c6158_456c_482b_9c8f_03d7360d8952_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_2c3c6158_456c_482b_9c8f_03d7360d8952_a1
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hNK, hK, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_2c3c6158_456c_482b_9c8f_03d7360d8952_a1 N hN
  exact ⟨K, hNK, hK,
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_2c3c6158_456c_482b_9c8f_03d7360d8952_a1 K hK hCard hMax⟩