-- Prove2me | solution 2 for WilliamsonShmoys.planar_graph_edge_bound_all__p2m_412cf563_cd90_4618_ba6d_11be264b4659_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:44:08.473277+00:00
-- url     : https://prove2.me/submissions/8d1befbf-2761-456a-b4d6-b925b458f851

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_afc05135_ebe6_4750_8043_cdffdef73084_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) :=
  WilliamsonShmoys.planar_edge_count_upper_bound__p2m_afc05135_ebe6_4750_8043_cdffdef73084_a1 H hcard hdraw