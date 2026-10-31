-- Prove2me | solution 3 for WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_1095f796_c580_4096_843f_cd051f083539_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:27:56.384319+00:00
-- url     : https://prove2.me/submissions/798de154-ad2d-469b-bfbc-42770aad3ce5

import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edgeSet_ncard_le

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planarDrawingOn_edgeSet_ncard_le K hV hK
