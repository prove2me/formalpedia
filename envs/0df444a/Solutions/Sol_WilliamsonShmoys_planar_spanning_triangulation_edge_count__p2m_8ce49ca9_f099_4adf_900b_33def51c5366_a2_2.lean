-- Prove2me | solution 2 for WilliamsonShmoys.planar_spanning_triangulation_edge_count__p2m_8ce49ca9_f099_4adf_900b_33def51c5366_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:31:50.341998+00:00
-- url     : https://prove2.me/submissions/ed6e103a-5215-450c-8519-59c3b63ec02d

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) : ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_has_triangulated_supergraph L hDraw hV
