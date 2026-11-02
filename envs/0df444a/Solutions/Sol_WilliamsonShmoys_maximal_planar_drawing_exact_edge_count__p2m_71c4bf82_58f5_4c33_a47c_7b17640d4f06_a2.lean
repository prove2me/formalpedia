-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_71c4bf82_58f5_4c33_a47c_7b17640d4f06_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:06:52.75653+00:00
-- url     : https://prove2.me/submissions/47d3bf03-8c47-4ce9-9d94-b1667c7f398c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_9987107f_9ded_4251_bab3_dd81d8d6e153_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_9987107f_9ded_4251_bab3_dd81d8d6e153_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N <= K → HasPlanarDrawingOn K → K = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     N.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  have hupper := WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_9987107f_9ded_4251_bab3_dd81d8d6e153_a1
    N hV hN
  have hlower := WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_9987107f_9ded_4251_bab3_dd81d8d6e153_a1
    N hV hN hmax
  omega