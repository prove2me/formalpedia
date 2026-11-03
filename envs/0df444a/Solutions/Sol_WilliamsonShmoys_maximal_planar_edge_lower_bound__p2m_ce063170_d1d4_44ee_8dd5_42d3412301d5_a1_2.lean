-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ce063170_d1d4_44ee_8dd5_42d3412301d5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:48:48.249208+00:00
-- url     : https://prove2.me/submissions/063d7984-0405-4478-9dd0-64330647fe18

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_eaae8083_26da_4ee8_a632_1917071465a8_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    3 * Fintype.card V <= L.edgeFinset.card + 6 :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_eaae8083_26da_4ee8_a632_1917071465a8_a1 L hL hmax hcard