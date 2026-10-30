-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_59c448d8_2415_4b81_b96a_4b978426d513_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:03:48.705293+00:00
-- url     : https://prove2.me/submissions/0ca3d498-78da-489a-b764-0b591d29f303

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_edge_count_planar_supergraph__p2m_61d32ba8_63e6_4051_9eef_c43df50e222b_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_has_exact_edge_count__p2m_61d32ba8_63e6_4051_9eef_c43df50e222b_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  obtain ⟨L, hKL, hDrawL, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_edge_count_planar_supergraph__p2m_61d32ba8_63e6_4051_9eef_c43df50e222b_a1
      K hDraw
  exact ⟨L, hKL, hDrawL,
    WilliamsonShmoys.maximal_planar_supergraph_has_exact_edge_count__p2m_61d32ba8_63e6_4051_9eef_c43df50e222b_a1
      K L hCard hKL hDrawL hMax⟩