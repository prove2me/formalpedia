-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_le_three_mul_card_sub_six__p2m_c8bd0d06_bddd_4d97_9a5a_50d50f58bad7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:16:21.680728+00:00
-- url     : https://prove2.me/submissions/65a6b428-2f97-409b-b042-3d0f572805ed

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    L.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1 L hplanar hV
