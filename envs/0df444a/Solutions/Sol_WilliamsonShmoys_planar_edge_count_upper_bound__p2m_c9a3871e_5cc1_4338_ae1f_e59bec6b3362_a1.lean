-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c9a3871e_5cc1_4338_ae1f_e59bec6b3362_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:51:23.976443+00:00
-- url     : https://prove2.me/submissions/186c5864-6c89-4bbd-93b8-f846a64240f3

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) : H.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_upper_bound H hH hV
