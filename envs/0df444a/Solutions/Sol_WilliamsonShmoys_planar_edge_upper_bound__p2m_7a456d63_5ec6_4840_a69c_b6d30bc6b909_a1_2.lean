-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_upper_bound__p2m_7a456d63_5ec6_4840_a69c_b6d30bc6b909_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:37:28.308357+00:00
-- url     : https://prove2.me/submissions/50050d17-8a48-413f-ab00-22793e7ec61d

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) : L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_count_bound_retry3 L hLplanar hV
