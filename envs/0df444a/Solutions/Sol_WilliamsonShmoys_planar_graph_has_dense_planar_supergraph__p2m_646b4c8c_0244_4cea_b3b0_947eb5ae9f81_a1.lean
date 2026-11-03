-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_dense_planar_supergraph__p2m_646b4c8c_0244_4cea_b3b0_947eb5ae9f81_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:32:46.863632+00:00
-- url     : https://prove2.me/submissions/b97299c1-cf8c-46b1-99ef-65dc86f45969

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_282f380d_4578_4570_b4a5_8b4767d8af92_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_dense__p2m_282f380d_4578_4570_b4a5_8b4767d8af92_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨K, hNK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_282f380d_4578_4570_b4a5_8b4767d8af92_a1 N hN
  exact ⟨K, hNK, hK,
    WilliamsonShmoys.edge_maximal_planar_graph_dense__p2m_282f380d_4578_4570_b4a5_8b4767d8af92_a1 K hK hcard hmax⟩