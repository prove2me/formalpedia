-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_85dfe40e_bf21_4653_aec5_d5293b86ee0f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:38:19.562078+00:00
-- url     : https://prove2.me/submissions/63c3d69d-abda-4aea-aba7-77f0ea479666

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1 G hG hV
