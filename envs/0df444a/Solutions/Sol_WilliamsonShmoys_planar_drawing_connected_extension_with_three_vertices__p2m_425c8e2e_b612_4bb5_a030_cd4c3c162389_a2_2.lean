-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_extension_with_three_vertices__p2m_425c8e2e_b612_4bb5_a030_cd4c3c162389_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:36:45.605646+00:00
-- url     : https://prove2.me/submissions/0f323888-024d-4964-a221-bdc83cc6b27f

import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph__p2m_a37fca92_b240_4415_b2f0_be56bbb8e59b_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K :=
  WilliamsonShmoys.planar_connected_supergraph__p2m_a37fca92_b240_4415_b2f0_be56bbb8e59b_a1 H hDraw hV
