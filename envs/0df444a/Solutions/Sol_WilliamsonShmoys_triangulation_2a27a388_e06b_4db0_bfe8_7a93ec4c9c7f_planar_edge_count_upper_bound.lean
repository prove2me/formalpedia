-- Prove2me | solution 1 for WilliamsonShmoys.triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_planar_edge_count_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:37:34.009191+00:00
-- url     : https://prove2.me/submissions/89fbd0e7-56a2-4fd4-8918-b6a04c73c912

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_d44225cd_db62_4aad_8e63_f30bd1a9ed2e_a1
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound__p2m_d44225cd_db62_4aad_8e63_f30bd1a9ed2e_a1 K hK hV