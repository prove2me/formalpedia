-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_27b8a194_6c54_4ca3_a684_9503cbbde751_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:51:17.41999+00:00
-- url     : https://prove2.me/submissions/5964abd6-d45a-4cec-91db-7786280c10da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_9d0fb3ab_d66a_4954_897e_7905864f2bd9_a1
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_count__p2m_9d0fb3ab_d66a_4954_897e_7905864f2bd9_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V) :
    J.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hPlanarH, hCount, hMax⟩ :=
    WilliamsonShmoys.planar_maximal_extension__p2m_9d0fb3ab_d66a_4954_897e_7905864f2bd9_a1
      J hPlanar
  have hBound :=
    WilliamsonShmoys.planar_maximal_edge_count__p2m_9d0fb3ab_d66a_4954_897e_7905864f2bd9_a1
      H hPlanarH hV hMax
  exact (Nat.add_le_add_right hCount 6).trans hBound