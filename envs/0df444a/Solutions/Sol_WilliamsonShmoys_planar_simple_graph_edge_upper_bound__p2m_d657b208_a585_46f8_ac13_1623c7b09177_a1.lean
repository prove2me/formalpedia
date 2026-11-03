-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_d657b208_a585_46f8_ac13_1623c7b09177_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:53:59.117751+00:00
-- url     : https://prove2.me/submissions/0b5c24d9-19b6-4480-941f-29dd1a596827

import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_d657b208_a585_46f8_ac13_1623c7b09177_a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel _
    G.edgeFinset.card <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_d657b208_a585_46f8_ac13_1623c7b09177_a2 G hG hcard