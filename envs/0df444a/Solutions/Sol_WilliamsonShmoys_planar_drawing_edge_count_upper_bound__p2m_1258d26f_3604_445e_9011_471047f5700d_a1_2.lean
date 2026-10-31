-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_1258d26f_3604_445e_9011_471047f5700d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:36:48.073305+00:00
-- url     : https://prove2.me/submissions/0220c35b-424b-4b89-be2a-242b7e033c37

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound K hK hV
