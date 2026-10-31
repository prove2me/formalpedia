-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_6fae641e_69bd_437f_8912_51466427af04_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:45:50.467519+00:00
-- url     : https://prove2.me/submissions/60afafdf-9220-4af2-a45e-b8bb63252e7e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_exists__p2m_3d35640d_f78d_47f5_a2d5_6e5c206bbbf4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected__p2m_3d35640d_f78d_47f5_a2d5_6e5c206bbbf4_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.Connected ∧ HasPlanarDrawingOn H := by
  obtain ⟨H, hGH, hCount, hH, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_3d35640d_f78d_47f5_a2d5_6e5c206bbbf4_a1
      G hG
  have hConnected :=
    WilliamsonShmoys.maximal_planar_drawing_connected__p2m_3d35640d_f78d_47f5_a2d5_6e5c206bbbf4_a1
      H hH hMax
  exact ⟨H, hGH, hCount, hConnected, hH⟩