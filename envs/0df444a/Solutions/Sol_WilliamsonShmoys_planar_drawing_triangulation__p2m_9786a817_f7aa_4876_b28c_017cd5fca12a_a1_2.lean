-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_triangulation__p2m_9786a817_f7aa_4876_b28c_017cd5fca12a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:17:25.803059+00:00
-- url     : https://prove2.me/submissions/c0eef9d2-393b-406b-aedc-5d24a1977cce

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_exists

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ T : SimpleGraph V, H ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧ T.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_exists H hV hDraw
