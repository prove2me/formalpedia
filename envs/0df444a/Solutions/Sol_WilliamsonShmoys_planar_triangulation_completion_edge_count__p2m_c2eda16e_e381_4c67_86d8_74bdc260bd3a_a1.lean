-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion_edge_count__p2m_c2eda16e_e381_4c67_86d8_74bdc260bd3a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:51:05.642291+00:00
-- url     : https://prove2.me/submissions/14f435d9-d7ac-4b80-b87a-c1e674cee672

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_0c9ddbae_e05c_4655_8aee_21825ef9cfbc_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_0c9ddbae_e05c_4655_8aee_21825ef9cfbc_a2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hMD, hMax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_0c9ddbae_e05c_4655_8aee_21825ef9cfbc_a2
      L hDraw
  exact ⟨M, hLM, hMD,
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_0c9ddbae_e05c_4655_8aee_21825ef9cfbc_a2
      M hV hMD hMax⟩