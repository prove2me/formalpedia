-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_e194ab00_41b0_4b4f_af08_d9da373e3f16_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:46:39.140523+00:00
-- url     : https://prove2.me/submissions/174daf0f-1bd2-4c04-b9da-472a902e49f3

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1 K hK hV
