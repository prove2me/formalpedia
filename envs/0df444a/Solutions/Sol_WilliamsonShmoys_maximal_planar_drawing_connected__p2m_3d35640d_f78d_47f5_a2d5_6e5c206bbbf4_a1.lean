-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_connected__p2m_3d35640d_f78d_47f5_a2d5_6e5c206bbbf4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:00:23.270983+00:00
-- url     : https://prove2.me/submissions/0d10bdae-4c19-4fa0-a87b-18fb0ef0e246
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_can_join_components__p2m_e94edbb5_ee29_49bb_b0f7_4813201733c6_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    H.Connected := by
  by_contra hDisc
  obtain ⟨K, hHK, hK, hnotKH⟩ :=
    WilliamsonShmoys.planar_drawing_can_join_components__p2m_e94edbb5_ee29_49bb_b0f7_4813201733c6_a1
      H hH hDisc
  exact hnotKH (hMax K hHK hK)