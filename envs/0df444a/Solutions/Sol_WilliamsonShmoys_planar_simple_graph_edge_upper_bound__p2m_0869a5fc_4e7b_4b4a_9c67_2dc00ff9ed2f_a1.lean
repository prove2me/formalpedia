-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_0869a5fc_4e7b_4b4a_9c67_2dc00ff9ed2f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:27:30.538047+00:00
-- url     : https://prove2.me/submissions/2b0de928-e9ab-4be2-a458-32785e0a063f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_7f8156d0_59cd_483d_b914_1d18d842c166_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hU : HasPlanarDrawingOn U)
    (hV : 3 ≤ Fintype.card V) :
    U.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  have h :=
    WilliamsonShmoys.planar_edge_bound__p2m_7f8156d0_59cd_483d_b914_1d18d842c166_a2
      U hU hV
  omega