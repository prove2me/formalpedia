-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_5a40a0c2_74f9_4570_bfa0_b6520ce4bb58_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:19:47.516217+00:00
-- url     : https://prove2.me/submissions/7f2d0da6-b5f9-4ad4-b047-7c49c69af41a

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_repair3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K) : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_edge_upper_bound_repair3 K hCard hK
