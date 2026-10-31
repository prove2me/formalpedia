-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_46cbd439_c8e2_447f_93cf_6418b9c298f0_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:19:23.807986+00:00
-- url     : https://prove2.me/submissions/3e294302-9943-458b-b360-fac0b8addd87

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) (hCard : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N) : N.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4 N hN hCard hmax
