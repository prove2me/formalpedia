-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_edge_count__p2m_05a50faf_c208_4b89_a21d_3d6ee49fb52f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:24:18.953182+00:00
-- url     : https://prove2.me/submissions/e625c235-8a44-4b91-9f9c-286414c5f9f0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_edge_maximal__p2m_7b09e600_7df3_4cde_9f3e_028247bb9b4a_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_7b09e600_7df3_4cde_9f3e_028247bb9b4a_a2
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      G <= H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V - 6 = H.edgeSet.ncard := by
  obtain ⟨H, hGH, hHplanar, hmax⟩ :=
    WilliamsonShmoys.planar_augmentation_edge_maximal__p2m_7b09e600_7df3_4cde_9f3e_028247bb9b4a_a2 G hplanar
  exact ⟨H, hGH, hHplanar,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_7b09e600_7df3_4cde_9f3e_028247bb9b4a_a2 H hHplanar hcard hmax⟩