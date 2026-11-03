-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_fc022252_a12f_4a07_aef3_b2bbba00d482_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:41:42.511968+00:00
-- url     : https://prove2.me/submissions/f3e20618-80ce-476e-ab56-29d3debd9706

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_upper_bound__p2m_b022b4b8_e7d5_474e_bb13_2a0e5909c103_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     K.edgeFinset.card <= 3 * Fintype.card V - 6) :=
  WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound__p2m_b022b4b8_e7d5_474e_bb13_2a0e5909c103_a1 K hcard hK