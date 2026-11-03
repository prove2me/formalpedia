-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_f2cfae8b_743a_4350_8c03_fa33aa7b455e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:37:34.500931+00:00
-- url     : https://prove2.me/submissions/70f3afa4-cd1a-40ed-b30f-26f166b3ddbf

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_upper_bound__p2m_b022b4b8_e7d5_474e_bb13_2a0e5909c103_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hcard : 3 <= Fintype.card V) : (letI : DecidableRel K.Adj := Classical.decRel K.Adj; K.edgeFinset.card <= 3 * Fintype.card V - 6) :=
  WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound__p2m_b022b4b8_e7d5_474e_bb13_2a0e5909c103_a1 K hcard hK