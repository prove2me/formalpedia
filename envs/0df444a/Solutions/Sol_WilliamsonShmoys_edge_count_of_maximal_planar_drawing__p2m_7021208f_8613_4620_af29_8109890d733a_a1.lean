-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_7021208f_8613_4620_af29_8109890d733a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:35:57.021947+00:00
-- url     : https://prove2.me/submissions/aebe1787-095e-42e9-910e-b357c2563265

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_of_drawing__p2m_6e927d54_05a0_4e04_9e4a_5cbec6b81d96_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_lower_of_maximality__p2m_6e927d54_05a0_4e04_9e4a_5cbec6b81d96_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall U : SimpleGraph V, T <= U -> WilliamsonShmoys.HasPlanarDrawingOn U -> U = T) :
    letI : DecidableRel T.Adj := Classical.decRel T.Adj
    T.edgeFinset.card + 6 = 3 * Fintype.card V := by
  letI : DecidableRel T.Adj := Classical.decRel T.Adj
  have hupper :=
    WilliamsonShmoys.planar_edge_count_upper_of_drawing__p2m_6e927d54_05a0_4e04_9e4a_5cbec6b81d96_a1
      T hT hcard
  have hlower :=
    WilliamsonShmoys.planar_edge_count_lower_of_maximality__p2m_6e927d54_05a0_4e04_9e4a_5cbec6b81d96_a1
      T hT hcard hmax
  omega