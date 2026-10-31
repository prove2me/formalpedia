-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_count_lower__p2m_ce0752f6_2cc0_436b_9908_f6f14786777a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:04:47.049795+00:00
-- url     : https://prove2.me/submissions/5d8b92e7-799d-4f5c-8615-24c5913302c9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_4efb3040_0ad8_4d1f_b560_f99843ee3860_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_4efb3040_0ad8_4d1f_b560_f99843ee3860_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      HasPlanarDrawingOn N ∧
      3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hNDraw, hMax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_4efb3040_0ad8_4d1f_b560_f99843ee3860_a1 M hDraw
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition__p2m_4efb3040_0ad8_4d1f_b560_f99843ee3860_a1 N hNDraw hMax hCard
  refine ⟨N, hMN, hNDraw, ?_⟩
  nlinarith