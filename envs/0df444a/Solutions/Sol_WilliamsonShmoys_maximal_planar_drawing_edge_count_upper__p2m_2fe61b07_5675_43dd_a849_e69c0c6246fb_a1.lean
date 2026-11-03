-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_upper__p2m_2fe61b07_5675_43dd_a849_e69c0c6246fb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:11:20.761888+00:00
-- url     : https://prove2.me/submissions/54ef4ace-8d5b-457c-8b38-b50ed33b8bd3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_401105e3_1529_4fdd_958a_7e12d53ff038_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    letI : DecidableRel N.Adj := Classical.decRel N.Adj
    N.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  exact WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_401105e3_1529_4fdd_958a_7e12d53ff038_a1 N hV hN
