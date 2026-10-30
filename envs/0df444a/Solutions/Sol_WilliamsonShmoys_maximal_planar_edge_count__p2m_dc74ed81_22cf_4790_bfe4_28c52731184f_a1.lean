-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_dc74ed81_22cf_4790_bfe4_28c52731184f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T12:06:27.452623+00:00
-- url     : https://prove2.me/submissions/ba7a3ab4-3816-4b8f-9942-27988036c284

import Theorems.Thm_WilliamsonShmoys_maximal_planar_upper_bound__p2m_f02ef8ad_5db5_4334_91a0_6b5d944fa80f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_lower_bound__p2m_f02ef8ad_5db5_4334_91a0_6b5d944fa80f_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeSet ⊆ L.edgeSet →
      L.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hu := WilliamsonShmoys.maximal_planar_upper_bound__p2m_f02ef8ad_5db5_4334_91a0_6b5d944fa80f_a1 K hK hV
  have hl := WilliamsonShmoys.maximal_planar_lower_bound__p2m_f02ef8ad_5db5_4334_91a0_6b5d944fa80f_a1 K hK hV hmax
  omega