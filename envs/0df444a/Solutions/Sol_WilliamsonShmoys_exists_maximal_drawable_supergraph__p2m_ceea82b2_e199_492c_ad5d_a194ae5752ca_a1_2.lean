-- Prove2me | solution 2 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_ceea82b2_e199_492c_ad5d_a194ae5752ca_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:48:52.327391+00:00
-- url     : https://prove2.me/submissions/825d15d8-0d57-4bc0-b5c0-a8d7666ca8af

import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ W : SimpleGraph V, G ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧ ∀ X : SimpleGraph V, W ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X = W :=
  WilliamsonShmoys.planar_maximal_extension__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3 G hG
