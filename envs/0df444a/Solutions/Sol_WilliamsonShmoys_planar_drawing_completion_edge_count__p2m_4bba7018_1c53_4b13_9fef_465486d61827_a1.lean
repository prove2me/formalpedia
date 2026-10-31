-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion_edge_count__p2m_4bba7018_1c53_4b13_9fef_465486d61827_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:10:57.730863+00:00
-- url     : https://prove2.me/submissions/9df0fb91-9caf-4068-9c0c-ee9066ffebac

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_supergraph__p2m_6a8f39b0_bd46_412b_a379_1f5e129b67f1_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6a8f39b0_bd46_412b_a379_1f5e129b67f1_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_6a8f39b0_bd46_412b_a379_1f5e129b67f1_a1
      H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_6a8f39b0_bd46_412b_a379_1f5e129b67f1_a1
      K hK hV hmax⟩