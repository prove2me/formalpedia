-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_77d68189_39bf_4e13_b3a3_9f804ba94476_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:39:28.41525+00:00
-- url     : https://prove2.me/submissions/eef31587-a2b6-4b9b-acbf-6526fb6a566c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_4d475df2_1a8a_43aa_9ce4_014b937605e8_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_4d475df2_1a8a_43aa_9ce4_014b937605e8_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G ≤ H ∧
      3 * Fintype.card V = H.edgeSet.ncard + 6 := by
  obtain ⟨H, hH, hGH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_4d475df2_1a8a_43aa_9ce4_014b937605e8_a1
      G hG
  exact ⟨H, hH, hGH,
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_4d475df2_1a8a_43aa_9ce4_014b937605e8_a1
      H hcard hH hmax⟩