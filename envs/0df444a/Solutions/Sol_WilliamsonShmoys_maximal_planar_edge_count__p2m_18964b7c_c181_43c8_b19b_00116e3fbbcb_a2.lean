-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_18964b7c_c181_43c8_b19b_00116e3fbbcb_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:25:49.639757+00:00
-- url     : https://prove2.me/submissions/99a65f50-0534-476f-b9b3-dd6d2eeea4b5

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_578e1ae6_405d_472f_8260_c63e86041167_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_578e1ae6_405d_472f_8260_c63e86041167_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V) [DecidableRel L.Adj],
      (∀ {u v}, K.Adj u v → L.Adj u v) →
      HasPlanarDrawingOn L →
      ∀ {u v}, L.Adj u v → K.Adj u v) :
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_578e1ae6_405d_472f_8260_c63e86041167_a1 K hK hV
  · exact WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_578e1ae6_405d_472f_8260_c63e86041167_a1 K hK hV hmax
