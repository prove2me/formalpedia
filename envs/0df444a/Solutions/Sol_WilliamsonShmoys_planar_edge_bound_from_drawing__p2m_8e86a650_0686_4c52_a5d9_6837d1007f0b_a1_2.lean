-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_bound_from_drawing__p2m_8e86a650_0686_4c52_a5d9_6837d1007f0b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:53:48.284204+00:00
-- url     : https://prove2.me/submissions/ecdb786a-23c4-473c-91e1-33aae6271591

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_77901df4_aad7_410f_861f_76a2bd150be4_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    G.edgeFinset.card + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_count_upper_bound__p2m_77901df4_aad7_410f_861f_76a2bd150be4_a1 G hcard hG