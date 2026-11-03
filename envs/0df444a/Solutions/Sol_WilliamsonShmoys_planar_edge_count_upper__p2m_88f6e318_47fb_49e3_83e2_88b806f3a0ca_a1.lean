-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper__p2m_88f6e318_47fb_49e3_83e2_88b806f3a0ca_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:12:54.876211+00:00
-- url     : https://prove2.me/submissions/33433d83-54cc-4ecd-bccf-36f78a9a1306

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_401105e3_1529_4fdd_958a_7e12d53ff038_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
     H.edgeFinset.card + 6 <= 3 * Fintype.card V) := by
  classical
  have h := WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_401105e3_1529_4fdd_958a_7e12d53ff038_a1 H hV hH
  omega
