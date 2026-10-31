-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_e4b54fa0_8696_482b_974e_2350a87956d8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:14:06.831531+00:00
-- url     : https://prove2.me/submissions/cbc59b3a-ddad-43af-b596-f4de72acd5fa

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_d113e12d_71ad_41a3_b6a2_eff564f35d28_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_d113e12d_71ad_41a3_b6a2_eff564f35d28_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hmax : ∀ R : SimpleGraph V, Q.edgeSet ⊆ R.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn R → R.edgeSet = Q.edgeSet) :
    Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_d113e12d_71ad_41a3_b6a2_eff564f35d28_a1 Q hV hDraw
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_d113e12d_71ad_41a3_b6a2_eff564f35d28_a1 Q hV hDraw hmax
  omega