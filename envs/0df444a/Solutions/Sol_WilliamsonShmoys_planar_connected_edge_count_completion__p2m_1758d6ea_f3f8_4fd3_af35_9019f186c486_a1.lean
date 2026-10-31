-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_count_completion__p2m_1758d6ea_f3f8_4fd3_af35_9019f186c486_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:15:27.542616+00:00
-- url     : https://prove2.me/submissions/89dd7659-29b3-4bff-8ea2-207887ad4a5d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_3e96e4b7_ffaf_421c_b46f_8949f4d2645c_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_3e96e4b7_ffaf_421c_b46f_8949f4d2645c_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hConn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hKH, hHPlanar, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension__p2m_3e96e4b7_ffaf_421c_b46f_8949f4d2645c_a2
      K hK
  have hHConn : H.Connected := hConn.mono hKH
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_3e96e4b7_ffaf_421c_b46f_8949f4d2645c_a2
      H hHPlanar hMax hHConn hV
  exact ⟨H, hKH, hHPlanar, hCount⟩