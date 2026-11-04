-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_6fbbf826_2147_4da9_aa49_9b6333f29881_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:24:52.859246+00:00
-- url     : https://prove2.me/submissions/8f5eaf64-4cfa-4168-8598-d36810e7f8f7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_planar_drawing_edge_count_upper__p2m_f064fab3_2a2a_43e1_9be9_e5e958f9fe83_a1
import Theorems.Thm_maximal_planar_drawing_edge_count_lower__p2m_f064fab3_2a2a_43e1_9be9_e5e958f9fe83_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeFinset.card + 6 = 3 * Fintype.card V := by
  have hupper :=
    planar_drawing_edge_count_upper__p2m_f064fab3_2a2a_43e1_9be9_e5e958f9fe83_a1
      K hK hcard
  have hlower :=
    maximal_planar_drawing_edge_count_lower__p2m_f064fab3_2a2a_43e1_9be9_e5e958f9fe83_a1
      K hK hmax hcard
  omega
