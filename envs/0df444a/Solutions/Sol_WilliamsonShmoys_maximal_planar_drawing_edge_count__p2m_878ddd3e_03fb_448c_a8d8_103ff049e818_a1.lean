-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_878ddd3e_03fb_448c_a8d8_103ff049e818_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:19:35.40298+00:00
-- url     : https://prove2.me/submissions/e878e85f-3010-45f2-aa84-122d49370c8b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_1258d26f_3604_445e_9011_471047f5700d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_1258d26f_3604_445e_9011_471047f5700d_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K)
    (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_1258d26f_3604_445e_9011_471047f5700d_a1 K hK hV
  have hLower := WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_1258d26f_3604_445e_9011_471047f5700d_a1 K hK hmax hV
  omega