-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_444cd434_7013_46bb_9e82_d756827f6b0e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:41:12.838399+00:00
-- url     : https://prove2.me/submissions/6ab861ce-a3e5-45b9-9cdb-c610e7a3e011

import Theorems.Thm_WilliamsonShmoys_planar_edge_card_upper_bound__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    K.edgeFinset.card <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_card_upper_bound__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1 K hcard hK