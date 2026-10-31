-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_edge_count__p2m_8fdb4f78_7a22_4d46_bd0b_609fa5b74b25_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:55:22.101156+00:00
-- url     : https://prove2.me/submissions/3e5cd8b8-3685-4e47-94ca-3b4410bbe385

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_maximal_extension__p2m_04736d40_a8e2_4a01_9968_14670118dd12_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_04736d40_a8e2_4a01_9968_14670118dd12_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_augmentation_maximal_extension__p2m_04736d40_a8e2_4a01_9968_14670118dd12_a1
      H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_04736d40_a8e2_4a01_9968_14670118dd12_a1
      K hK hV hmax⟩