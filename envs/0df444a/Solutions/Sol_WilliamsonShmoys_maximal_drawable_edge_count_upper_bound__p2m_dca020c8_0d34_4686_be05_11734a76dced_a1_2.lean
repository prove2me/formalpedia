-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_edge_count_upper_bound__p2m_dca020c8_0d34_4686_be05_11734a76dced_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:07:53.546004+00:00
-- url     : https://prove2.me/submissions/da2bfb6f-ebc9-48ca-ba02-4c5db726540d

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q) (hV : 3 ≤ Fintype.card V) : Q.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_upper_bound Q hDraw hV
