-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_f8388283_f9ed_4c0f_b0f7_c6403411f5ff_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:53:27.139337+00:00
-- url     : https://prove2.me/submissions/787c4df7-3af1-4e12-a313-c33a475c85e9

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X) (hV : 3 ≤ Fintype.card V) : X.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1 X hX hV
