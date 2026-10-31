-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_18203136_f8d0_4c28_bbe0_f08319907a9f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:03:28.321992+00:00
-- url     : https://prove2.me/submissions/e3bfc5b0-7d4f-4b4d-8020-def657e85e03

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_has_triangulated_supergraph G hDraw hV
