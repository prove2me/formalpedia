-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_edge_count_upper__p2m_19c9eeac_1bda_4675_8c1b_5590acff2ab1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:20:42.296552+00:00
-- url     : https://prove2.me/submissions/60869513-bc92-4c95-ae2d-084e8094d61a

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R) (hV : 3 <= Fintype.card V) : R.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_upper_bound R hDraw hV
