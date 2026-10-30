-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_2727cf65_1722_4248_9cab_723efcbdd93a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:33:03.239641+00:00
-- url     : https://prove2.me/submissions/2af6a9e0-810a-4fc8-a9b9-e490bd8a06b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper__p2m_6b45552a_e614_43a1_bcb2_5a02dc98d5fe_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_6b45552a_e614_43a1_bcb2_5a02dc98d5fe_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ H' : SimpleGraph V, H ≤ H' → H' ≠ H →
      ¬ HasPlanarDrawingOn H')
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_6b45552a_e614_43a1_bcb2_5a02dc98d5fe_a2 H hDraw hV
  have hLower := WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_6b45552a_e614_43a1_bcb2_5a02dc98d5fe_a2 H hDraw hMax hV
  omega