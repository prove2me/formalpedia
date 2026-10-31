-- Prove2me | solution 1 for WilliamsonShmoys.triangulated_planar_supergraph__p2m_e16fd743_6daf_4b1b_8baa_fc8319a376a6_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:00:44.751975+00:00
-- url     : https://prove2.me/submissions/b3d2de76-3b4f-496c-b122-65e18084b8dd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_ebb4e414_4dfa_4f3a_826b_c9f7b30cda57_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_ebb4e414_4dfa_4f3a_826b_c9f7b30cda57_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      M ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hMH, hHdraw, hMax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_ebb4e414_4dfa_4f3a_826b_c9f7b30cda57_a1
      M hDraw
  have hEdges :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_ebb4e414_4dfa_4f3a_826b_c9f7b30cda57_a1
      H hHdraw hV hMax
  exact ⟨H, hMH, hHdraw, hEdges⟩
