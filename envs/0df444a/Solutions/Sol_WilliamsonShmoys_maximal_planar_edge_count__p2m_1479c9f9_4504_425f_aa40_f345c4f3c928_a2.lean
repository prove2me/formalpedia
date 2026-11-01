-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_1479c9f9_4504_425f_aa40_f345c4f3c928_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:55:02.744675+00:00
-- url     : https://prove2.me/submissions/f2d5062c-8985-487f-b378-7f28916c4642
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_d4d2ff2f_8400_446a_8d4e_186156e78298_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_d4d2ff2f_8400_446a_8d4e_186156e78298_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      3 * Fintype.card V - 6 = K.edgeFinset.card) := by
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hupper :
      K.edgeFinset.card ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_d4d2ff2f_8400_446a_8d4e_186156e78298_a2
      K hK hcard
  have hlower :
      3 * Fintype.card V - 6 ≤ K.edgeFinset.card :=
    WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_d4d2ff2f_8400_446a_8d4e_186156e78298_a2
      K hK hmax hcard
  omega