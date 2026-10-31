-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_4c97134d_4021_4fb3_9ace_f88e43ef34b2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:47:04.627123+00:00
-- url     : https://prove2.me/submissions/1f4de7cc-bfb7-4979-ae4f-9dd046f21ca5

import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H :=
  WilliamsonShmoys.planar_maximal_extension__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3 G hG
