-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_e3ce4704_f609_45f0_9a05_cff1f4f992c7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:34:44.961774+00:00
-- url     : https://prove2.me/submissions/7421f09a-3ad5-4450-b8ff-450ce3dd70c5

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_extension G hG hV
