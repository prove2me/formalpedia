-- Prove2me | solution 2 for WilliamsonShmoys.exists_isMaximalPlanarSupergraph__p2m_252969a2_5705_4ea9_b97e_d995b4f5b608_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:42:25.514996+00:00
-- url     : https://prove2.me/submissions/585afe12-589d-438c-b94e-ad0fd8dc98c3

import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M :=
  WilliamsonShmoys.planar_maximal_extension__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3 L hDraw
