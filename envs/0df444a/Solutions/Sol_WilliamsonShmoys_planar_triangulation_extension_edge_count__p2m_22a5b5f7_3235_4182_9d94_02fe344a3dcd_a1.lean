-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_22a5b5f7_3235_4182_9d94_02fe344a3dcd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:48:16.238396+00:00
-- url     : https://prove2.me/submissions/a373ea51-2fba-41d6-8db6-4a7d2fc3abcc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edgeMaximalPlanarSupergraph__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a3__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a4
import Theorems.Thm_WilliamsonShmoys_edgeMaximalPlanar_edgeCount__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a3__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a4

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hDraw : HasPlanarDrawingOn G) :
    ∃ N : SimpleGraph V, G <= N ∧ HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hGN, hNDraw, hMax⟩ :=
    WilliamsonShmoys.exists_edgeMaximalPlanarSupergraph__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a3__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a4
      G hDraw
  exact ⟨N, hGN, hNDraw,
    WilliamsonShmoys.edgeMaximalPlanar_edgeCount__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a3__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a4
      N hV hNDraw hMax⟩