-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_bd652ef6_f935_4766_81fb_919843a61889_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:32:47.273489+00:00
-- url     : https://prove2.me/submissions/408c0cc8-46bb-496a-9dd2-8990ac73aa7b

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Y : SimpleGraph V) (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) (hV : 3 ≤ Fintype.card V) : Y.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1 Y hY hV
