-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_extension__p2m_22c09847_b733_4661_b230_9655792a93fd_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:36:49.854576+00:00
-- url     : https://prove2.me/submissions/fb5f17ba-3eb8-4922-94e3-04f34b293bb7

import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H :=
  WilliamsonShmoys.planar_maximal_extension__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3 G hG
