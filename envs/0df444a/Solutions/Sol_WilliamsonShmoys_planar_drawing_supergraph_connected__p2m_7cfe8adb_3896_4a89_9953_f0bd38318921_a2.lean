-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_supergraph_connected__p2m_7cfe8adb_3896_4a89_9953_f0bd38318921_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:48:48.762535+00:00
-- url     : https://prove2.me/submissions/e2c4ae42-aff2-4989-96e1-7a0f154a13a4

import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph__p2m_a37fca92_b240_4415_b2f0_be56bbb8e59b_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X) (hV : 3 ≤ Fintype.card V) : ∃ Y : SimpleGraph V, X.edgeSet ⊆ Y.edgeSet ∧ Y.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn Y :=
  WilliamsonShmoys.planar_connected_supergraph__p2m_a37fca92_b240_4415_b2f0_be56bbb8e59b_a1 X hX hV
