-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulated_edge_count__p2m_585fc207_795e_4bf8_b875_c8bd05631f21_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:04:39.060888+00:00
-- url     : https://prove2.me/submissions/bb72f9ad-2c14-47f4-940f-3df672e385e5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_c0cea038_5072_4638_ab37_572b27cc73e9_a1
import Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_edge_count__p2m_c0cea038_5072_4638_ab37_572b27cc73e9_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hMax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_c0cea038_5072_4638_ab37_572b27cc73e9_a1 L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.inclusion_maximal_planar_edge_count__p2m_c0cea038_5072_4638_ab37_572b27cc73e9_a1 M hCard hM hMax⟩