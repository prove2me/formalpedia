-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_fd310935_5091_4856_a806_c268ac2a777f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:27:19.298989+00:00
-- url     : https://prove2.me/submissions/893b61e7-fa28-4cdf-b1e3-a54f52980080

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