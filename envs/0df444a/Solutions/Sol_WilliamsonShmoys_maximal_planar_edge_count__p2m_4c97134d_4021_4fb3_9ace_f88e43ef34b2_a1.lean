-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_4c97134d_4021_4fb3_9ace_f88e43ef34b2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:51:21.862031+00:00
-- url     : https://prove2.me/submissions/af44b930-303e-495f-8684-5930a542bfd9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_of_drawing__p2m_fcb8ec4c_c30d_44dd_a4d8_def1801ee290_a2
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_lower_of_maximal_drawing__p2m_fcb8ec4c_c30d_44dd_a4d8_def1801ee290_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_edge_count_upper_of_drawing__p2m_fcb8ec4c_c30d_44dd_a4d8_def1801ee290_a2
      H hCard hH
  · exact WilliamsonShmoys.planar_edge_count_lower_of_maximal_drawing__p2m_fcb8ec4c_c30d_44dd_a4d8_def1801ee290_a2
      H hCard hH hmax
