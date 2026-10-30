-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_b4f3c7d0_f80f_4201_8b80_29190a270a03_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:13:15.065563+00:00
-- url     : https://prove2.me/submissions/391562ec-c7c2-407c-bf64-65c4ce0726af

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_exists__p2m_d1313f94_0954_4f2e_9b9e_c37a9ebd0ec4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_d1313f94_0954_4f2e_9b9e_c37a9ebd0ec4_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hM, hMax⟩ :=
    WilliamsonShmoys.maximal_planar_extension_exists__p2m_d1313f94_0954_4f2e_9b9e_c37a9ebd0ec4_a1
      L hL hCard
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_d1313f94_0954_4f2e_9b9e_c37a9ebd0ec4_a1
      M hM hCard hMax
  exact ⟨M, hLM, hM, hCount⟩