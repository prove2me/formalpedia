-- Prove2me | solution 1 for WilliamsonShmoys.planar_connectivity_augmentation__p2m_0268dd7c_b22a_4ecf_a4e7_1329a8208a94_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:35:07.780663+00:00
-- url     : https://prove2.me/submissions/c8ba980b-af4f-497f-a149-7e4524313859
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_connected__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hGH, hHPlanar, hMaximal⟩ :=
    WilliamsonShmoys.planar_maximal_extension__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3
      G hG
  have hConnected :=
    WilliamsonShmoys.maximal_planar_connected__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3
      H hHPlanar hMaximal
  exact ⟨H, hGH, hConnected, hHPlanar⟩
