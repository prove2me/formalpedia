-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_count__p2m_84adf8d9_4f64_48f0_b013_da49e941db87_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:58:28.261268+00:00
-- url     : https://prove2.me/submissions/4af7e684-61d3-4e9e-9b10-2b802386c34b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_21bb1f42_93f8_4aca_8bd1_86213d966802_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_21bb1f42_93f8_4aca_8bd1_86213d966802_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_21bb1f42_93f8_4aca_8bd1_86213d966802_a1
      K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_21bb1f42_93f8_4aca_8bd1_86213d966802_a1
      L hL hmax hCard⟩