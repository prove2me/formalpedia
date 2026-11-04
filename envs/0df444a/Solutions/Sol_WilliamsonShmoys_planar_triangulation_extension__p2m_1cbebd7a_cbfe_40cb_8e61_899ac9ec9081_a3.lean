-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_1cbebd7a_cbfe_40cb_8e61_899ac9ec9081_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:12:56.812971+00:00
-- url     : https://prove2.me/submissions/4ed379a2-a6e2-482d-a844-918902cc94c3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_6fbbf826_2147_4da9_aa49_9b6333f29881_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6fbbf826_2147_4da9_aa49_9b6333f29881_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      ∃ (hKd : DecidableRel K.Adj),
        (letI : DecidableRel K.Adj := hKd;
          K.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨K, hNK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6fbbf826_2147_4da9_aa49_9b6333f29881_a1
      N hN
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  refine ⟨K, hNK, hK, ⟨inferInstance, ?_⟩⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_6fbbf826_2147_4da9_aa49_9b6333f29881_a1
    K hK hmax hcard
