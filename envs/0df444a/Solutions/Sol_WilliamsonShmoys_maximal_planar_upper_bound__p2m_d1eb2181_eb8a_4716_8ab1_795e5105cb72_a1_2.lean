-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_upper_bound__p2m_d1eb2181_eb8a_4716_8ab1_795e5105cb72_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:06:55.095251+00:00
-- url     : https://prove2.me/submissions/2642f1ec-f4e7-4bc2-8372-93029be6510e

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) : H.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound H hH hV
