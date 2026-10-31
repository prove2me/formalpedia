-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound__p2m_cf44c216_3f6e_4f0d_9ff9_4dc3d94f14d1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:29:12.201986+00:00
-- url     : https://prove2.me/submissions/4afab8e0-90f5-49a2-8e7a-bf619acc3335

import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edgeSet_ncard_le

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : K.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planarDrawingOn_edgeSet_ncard_le K hV hK
