-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_upper__p2m_620608d3_0799_426b_beeb_eff4e8e41716_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:18:35.157311+00:00
-- url     : https://prove2.me/submissions/eb7432a9-2eb2-4da8-8e12-6cd419b7c6fa

import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_5a40a0c2_74f9_4570_bfa0_b6520ce4bb58_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_5a40a0c2_74f9_4570_bfa0_b6520ce4bb58_a1 K hcard hK
