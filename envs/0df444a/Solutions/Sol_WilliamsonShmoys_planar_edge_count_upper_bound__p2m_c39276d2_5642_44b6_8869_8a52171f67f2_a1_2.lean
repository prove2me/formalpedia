-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c39276d2_5642_44b6_8869_8a52171f67f2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:59:10.841996+00:00
-- url     : https://prove2.me/submissions/957ff9ef-0f6e-456f-be37-91ba5e25bce1

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_count_bound_retry3 K hDraw hV
