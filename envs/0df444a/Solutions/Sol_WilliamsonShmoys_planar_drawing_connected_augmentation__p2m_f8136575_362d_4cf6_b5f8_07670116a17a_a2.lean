-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_f8136575_362d_4cf6_b5f8_07670116a17a_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:21:18.221208+00:00
-- url     : https://prove2.me/submissions/7c86b201-500a-4437-8013-78202d7d63e6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge_between_components__p2m_6542605d_05b7_4349_89df_2d6e0eb6b2d4_a1
import Theorems.Thm_WilliamsonShmoys_finite_planar_bridge_iteration__p2m_6542605d_05b7_4349_89df_2d6e0eb6b2d4_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  exact WilliamsonShmoys.finite_planar_bridge_iteration__p2m_6542605d_05b7_4349_89df_2d6e0eb6b2d4_a1
    G hplanar hcard (by
      intro K hGK hKplanar hKdisconnected
      exact WilliamsonShmoys.planar_drawing_add_bridge_between_components__p2m_6542605d_05b7_4349_89df_2d6e0eb6b2d4_a1
        K hKplanar hKdisconnected)