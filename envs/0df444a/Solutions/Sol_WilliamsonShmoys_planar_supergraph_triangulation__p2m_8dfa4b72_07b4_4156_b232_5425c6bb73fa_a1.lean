-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation__p2m_8dfa4b72_07b4_4156_b232_5425c6bb73fa_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:55:57.352911+00:00
-- url     : https://prove2.me/submissions/1a889e2f-9a55-4fe2-bd95-d1b6268dea69

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_extension__p2m_5fdd342d_dc75_47e0_8287_8202cedefb2b_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5fdd342d_dc75_47e0_8287_8202cedefb2b_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ := WilliamsonShmoys.planar_supergraph_extension__p2m_5fdd342d_dc75_47e0_8287_8202cedefb2b_a1 K hK
  have hcount := WilliamsonShmoys.maximal_planar_edge_count__p2m_5fdd342d_dc75_47e0_8287_8202cedefb2b_a1 L hCard hL hmax
  exact ⟨L, hKL, hL, hcount⟩