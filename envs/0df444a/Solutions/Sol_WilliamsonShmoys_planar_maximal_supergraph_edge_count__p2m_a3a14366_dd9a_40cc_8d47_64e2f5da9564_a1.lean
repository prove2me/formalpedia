-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph_edge_count__p2m_a3a14366_dd9a_40cc_8d47_64e2f5da9564_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:03:58.798127+00:00
-- url     : https://prove2.me/submissions/c6ee7a23-abd2-4be7-a559-d1c941fe2d17

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_10e3a5b8_1f49_4831_b4a7_c5e9b9512625_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_10e3a5b8_1f49_4831_b4a7_c5e9b9512625_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hMDraw, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_10e3a5b8_1f49_4831_b4a7_c5e9b9512625_a1
      L hDraw hV
  refine ⟨M, hLM, hMDraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_10e3a5b8_1f49_4831_b4a7_c5e9b9512625_a1
    M hMDraw hMax hV