-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_a4df0fa7_688f_4bd0_bfe4_ea6603f7e8eb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:32:52.038754+00:00
-- url     : https://prove2.me/submissions/a6abb914-d4a0-4886-9db3-1b7288eadc73

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_with_property__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a1__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a2
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_subgraph__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a1__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ P : SimpleGraph V,
      K.edgeSet ⊆ P.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      ∀ L : SimpleGraph V,
        P.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet ⊆ P.edgeSet := by
  obtain ⟨P, hKP, hP, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_supergraph_with_property__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a1__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a2
      K WilliamsonShmoys.HasPlanarDrawingOn hK
      (by
        intro G H hHG hG
        exact WilliamsonShmoys.planarDrawingOn_subgraph__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a1__p2m_fe6641dc_c570_459f_b36e_e7aed3590a75_a2
          hHG hG)
  exact ⟨P, hKP, hP, hmax⟩