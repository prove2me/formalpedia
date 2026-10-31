-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_d113e12d_71ad_41a3_b6a2_eff564f35d28_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:20:37.733995+00:00
-- url     : https://prove2.me/submissions/def6663c-9a83-4481-ab12-6206fd49ad22

import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edgeSet_ncard_le

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn Q) : Q.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planarDrawingOn_edgeSet_ncard_le Q hV hDraw
