-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_28646a36_1b88_4c0c_9520_4ba110528cb4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:48:16.145785+00:00
-- url     : https://prove2.me/submissions/fbb0b1d0-48bf-441f-b813-7949c53bcf33

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper__p2m_9c5c2913_8662_47f3_b676_c48b7de0b279_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count_lower__p2m_9c5c2913_8662_47f3_b676_c48b7de0b279_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M)
    (hCard : 3 <= Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_9c5c2913_8662_47f3_b676_c48b7de0b279_a1
      M hDraw hCard
  have hLower :=
    WilliamsonShmoys.maximal_drawing_edge_count_lower__p2m_9c5c2913_8662_47f3_b676_c48b7de0b279_a1
      M hDraw hMax hCard
  omega