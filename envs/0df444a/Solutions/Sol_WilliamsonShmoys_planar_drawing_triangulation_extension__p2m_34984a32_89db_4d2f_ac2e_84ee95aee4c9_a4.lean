-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_34984a32_89db_4d2f_ac2e_84ee95aee4c9_a4
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:51:08.261564+00:00
-- url     : https://prove2.me/submissions/a4f3f44d-48bc-4e40-822d-aa8990f2771e

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_extension_edge_count

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V) : ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧ N.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulated_extension_edge_count M hM hV
