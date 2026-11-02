-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_9987107f_9ded_4251_bab3_dd81d8d6e153_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:27:12.170819+00:00
-- url     : https://prove2.me/submissions/1a3c4c01-cbec-477c-b900-65b5450b58ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_on_edge_bound__p2m_ceac07bf_1e4c_4add_b38a_2aeb9fce6a2e_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N <= K → HasPlanarDrawingOn K → K = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     3 * Fintype.card V <= N.edgeFinset.card + 6) := by
  exact WilliamsonShmoys.planar_drawing_on_edge_bound__p2m_ceac07bf_1e4c_4add_b38a_2aeb9fce6a2e_a1 N hN