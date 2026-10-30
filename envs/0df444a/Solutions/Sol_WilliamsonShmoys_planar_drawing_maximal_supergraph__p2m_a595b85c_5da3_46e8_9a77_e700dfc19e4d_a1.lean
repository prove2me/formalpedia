-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_a595b85c_5da3_46e8_9a77_e700dfc19e4d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:20:40.94876+00:00
-- url     : https://prove2.me/submissions/253a21ab-73fd-4491-90d9-c65f87123ca5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_card_maximal_supergraph__p2m_c52ebc15_be26_4087_8cea_444a38292ff2_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ H : SimpleGraph V,
      N.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) ∧
      N.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hNH, hH, hmax, hcard⟩ :=
    WilliamsonShmoys.exists_card_maximal_supergraph__p2m_c52ebc15_be26_4087_8cea_444a38292ff2_a1
      N WilliamsonShmoys.HasPlanarDrawingOn hN
  exact ⟨H, hNH, hH, hmax, hcard⟩