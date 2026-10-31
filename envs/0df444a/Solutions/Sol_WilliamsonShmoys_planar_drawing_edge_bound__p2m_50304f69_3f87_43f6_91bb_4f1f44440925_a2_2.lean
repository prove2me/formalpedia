-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_50304f69_3f87_43f6_91bb_4f1f44440925_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:11:21.983049+00:00
-- url     : https://prove2.me/submissions/db99d895-b5ae-4228-bc81-25f0b135641e

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hDraw : HasPlanarDrawingOn S) (hV : 3 <= Fintype.card V) : S.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_upper_bound S hDraw hV
