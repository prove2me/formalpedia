-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_82e54da5_16cf_4d16_b293_9f40ba57f2f4_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:11:30.796845+00:00
-- url     : https://prove2.me/submissions/76c59b14-2a43-4ae7-8f39-6449d74aa046

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_b320f89e_6adf_4c95_8da8_b179076388d4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_b320f89e_6adf_4c95_8da8_b179076388d4_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    exists N : SimpleGraph V,
      M <= N /\
      WilliamsonShmoys.HasPlanarDrawingOn N /\
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hNPlanar, hNmax⟩ :=
    WilliamsonShmoys.planar_maximal_extension__p2m_b320f89e_6adf_4c95_8da8_b179076388d4_a1
      M hM hCard
  exact ⟨N, hMN, hNPlanar,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_b320f89e_6adf_4c95_8da8_b179076388d4_a1
      N hNPlanar hCard hNmax⟩