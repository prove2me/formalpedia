-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_count_upper_bound__p2m_c23ffc9b_3ccd_4354_ad9d_982ada7aecad_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:25:26.522438+00:00
-- url     : https://prove2.me/submissions/5d468d71-5e75-4ed0-b0f0-0a70b046f041

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_upper_bound H hH hV
