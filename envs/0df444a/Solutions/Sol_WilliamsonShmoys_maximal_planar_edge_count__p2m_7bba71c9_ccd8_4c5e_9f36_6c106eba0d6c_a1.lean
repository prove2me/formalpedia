-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_7bba71c9_ccd8_4c5e_9f36_6c106eba0d6c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:03:28.459136+00:00
-- url     : https://prove2.me/submissions/abf16f4b-af7f-4a8a-a4b8-b13f0d881128

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_88f6e318_47fb_49e3_83e2_88b806f3a0ca_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_lower__p2m_88f6e318_47fb_49e3_83e2_88b806f3a0ca_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
     H.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hupper := planar_edge_count_upper__p2m_88f6e318_47fb_49e3_83e2_88b806f3a0ca_a1 H hV hH
  have hlower := planar_edge_count_lower__p2m_88f6e318_47fb_49e3_83e2_88b806f3a0ca_a1 H hV hH hmax
  omega