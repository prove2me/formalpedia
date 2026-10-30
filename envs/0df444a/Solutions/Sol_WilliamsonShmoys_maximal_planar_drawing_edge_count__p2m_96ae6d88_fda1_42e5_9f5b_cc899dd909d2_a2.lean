-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_96ae6d88_fda1_42e5_9f5b_cc899dd909d2_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:32:07.775618+00:00
-- url     : https://prove2.me/submissions/a32c775f-fc54-4a8a-ac62-3bc44e8f4b22

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_3fec8f0c_c3a7_4eba_b2f0_d2b6c5de2dde_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_3fec8f0c_c3a7_4eba_b2f0_d2b6c5de2dde_a3

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_drawing_edge_bound__p2m_3fec8f0c_c3a7_4eba_b2f0_d2b6c5de2dde_a3
      H hH hCard
  have hLower : 3 * Fintype.card V ≤ H.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_3fec8f0c_c3a7_4eba_b2f0_d2b6c5de2dde_a3
      H hH hMax hCard
  omega