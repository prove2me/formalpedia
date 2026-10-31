-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_af1e49eb_be12_4828_9ecb_8639ecce9cdd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:50:23.987984+00:00
-- url     : https://prove2.me/submissions/cc6aa3b9-ed9a-44d6-9cce-4d220b2a3a61

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_count_completion__p2m_4d6c0a35_6002_42fd_b1db_c7f140706d86_a1
import Theorems.Thm_WilliamsonShmoys_maximal_supergraph_edgeSet_ncard_eq__p2m_4d6c0a35_6002_42fd_b1db_c7f140706d86_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hMDraw, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_has_edge_count_completion__p2m_4d6c0a35_6002_42fd_b1db_c7f140706d86_a1
      L hDraw hV
  have hSameCard :=
    WilliamsonShmoys.maximal_supergraph_edgeSet_ncard_eq__p2m_4d6c0a35_6002_42fd_b1db_c7f140706d86_a1
      L M hMax hLM hMDraw
  omega