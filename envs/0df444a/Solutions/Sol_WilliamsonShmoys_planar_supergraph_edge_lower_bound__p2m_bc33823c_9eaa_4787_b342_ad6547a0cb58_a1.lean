-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_bc33823c_9eaa_4787_b342_ad6547a0cb58_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:58:24.96298+00:00
-- url     : https://prove2.me/submissions/31d0bca8-28a8-4cc0-ac6c-c68e2047c77b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_6d3b2982_65b7_41de_b042_0682b8cb7f57_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_6d3b2982_65b7_41de_b042_0682b8cb7f57_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      N ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
      3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by
  obtain ⟨P, hNP, hP, hMax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal__p2m_6d3b2982_65b7_41de_b042_0682b8cb7f57_a1 N hN
  exact ⟨P, hNP, hP,
    WilliamsonShmoys.maximal_planar_edge_bound__p2m_6d3b2982_65b7_41de_b042_0682b8cb7f57_a1
      P hCard hP hMax⟩