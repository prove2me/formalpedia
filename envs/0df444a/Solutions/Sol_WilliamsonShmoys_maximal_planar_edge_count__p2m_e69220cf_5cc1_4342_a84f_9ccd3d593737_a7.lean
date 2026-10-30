-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_e69220cf_5cc1_4342_a84f_9ccd3d593737_a7
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T04:23:45.340987+00:00
-- url     : https://prove2.me/submissions/81ddfd44-a089-4cba-93cc-31d2e7028d2f

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_le__p2m_6af46978_2916_4816_b606_4f4cb75b2f24_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_ge__p2m_6af46978_2916_4816_b606_4f4cb75b2f24_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V,
      L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) :
    3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.maximal_planar_edge_count_ge__p2m_6af46978_2916_4816_b606_4f4cb75b2f24_a1
      L hV hL hmax
  · exact WilliamsonShmoys.planar_edge_count_le__p2m_6af46978_2916_4816_b606_4f4cb75b2f24_a1
      L hV hL