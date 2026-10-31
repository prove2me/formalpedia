-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_ec6e17da_f4f8_4b4d_9b03_c6a0a660eda4_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:22:21.175991+00:00
-- url     : https://prove2.me/submissions/0cf1bcc7-1c09-4dcc-a994-67245cf5ebe4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_27b8a194_6c54_4ca3_a684_9503cbbde751_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_27b8a194_6c54_4ca3_a684_9503cbbde751_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, J ≤ K → HasPlanarDrawingOn K → K ≤ J) :
    J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper : J.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_edge_count_upper_bound__p2m_27b8a194_6c54_4ca3_a684_9503cbbde751_a1
      J hPlanar hV
  have hLower : 3 * Fintype.card V ≤ J.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_27b8a194_6c54_4ca3_a684_9503cbbde751_a1
      J hPlanar hV hMax
  omega