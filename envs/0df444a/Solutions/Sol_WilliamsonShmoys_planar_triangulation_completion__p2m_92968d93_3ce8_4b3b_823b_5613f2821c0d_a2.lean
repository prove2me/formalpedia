-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_92968d93_3ce8_4b3b_823b_5613f2821c0d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:04:50.094791+00:00
-- url     : https://prove2.me/submissions/72885215-9339-4f7e-85a9-ffc496e5f437

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_2caa5445_5382_49b4_aef1_d1703ac143a6_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_2caa5445_5382_49b4_aef1_d1703ac143a6_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      R ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hRH, hH, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_2caa5445_5382_49b4_aef1_d1703ac143a6_a1
      R hR
  refine ⟨H, hRH, hH, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_2caa5445_5382_49b4_aef1_d1703ac143a6_a1
    H hH hCard hmax