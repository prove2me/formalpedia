-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_b5de7163_4173_4d75_853e_5e2f32ae30ae_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:13:20.116767+00:00
-- url     : https://prove2.me/submissions/52442143-024a-4c96-b0be-6b542f7e6fed

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_19f31498_c1c5_41a0_a186_562a063d6dde

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count_19f31498_c1c5_41a0_a186_562a063d6dde H hcard hplanar hmax
