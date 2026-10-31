-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_d113e12d_71ad_41a3_b6a2_eff564f35d28_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:16:41.556994+00:00
-- url     : https://prove2.me/submissions/dfd9317f-3602-4af9-9d69-acbdcccba34c

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_c924e691_b064_42cd_9f9f_84343d32d225_a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn Q) (hmax : ∀ R : SimpleGraph V, Q.edgeSet ⊆ R.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn R → R.edgeSet = Q.edgeSet) : 3 * Fintype.card V - 6 ≤ Q.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c924e691_b064_42cd_9f9f_84343d32d225_a2 Q hV hDraw hmax
