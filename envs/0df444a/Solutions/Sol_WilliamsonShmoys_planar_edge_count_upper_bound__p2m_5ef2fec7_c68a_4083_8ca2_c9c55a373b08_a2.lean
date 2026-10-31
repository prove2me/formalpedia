-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_5ef2fec7_c68a_4083_8ca2_c9c55a373b08_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:19:15.162061+00:00
-- url     : https://prove2.me/submissions/8ccf5233-4017-48a0-b9ca-bbf79bc967b0

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (W : SimpleGraph V) (hW : WilliamsonShmoys.HasPlanarDrawingOn W) (hV : 3 ≤ Fintype.card V) : W.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1 W hW hV
