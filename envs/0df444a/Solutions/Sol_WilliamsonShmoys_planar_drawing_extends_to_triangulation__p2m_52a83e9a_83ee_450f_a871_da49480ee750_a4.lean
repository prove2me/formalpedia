-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extends_to_triangulation__p2m_52a83e9a_83ee_450f_a871_da49480ee750_a4
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:31:51.489388+00:00
-- url     : https://prove2.me/submissions/2c52c239-2baf-4a80-8861-a0e66797fcd1

import Theorems.Thm_WilliamsonShmoys_planar_drawing_nat_edge_count_completion

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ L.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_nat_edge_count_completion K hDraw hV
