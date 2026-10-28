-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation_edge_monotone
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:07:12.751181+00:00
-- url     : https://prove2.me/submissions/ba14fbba-c086-4e41-975a-937a53950bb9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected
import Theorems.Thm_WilliamsonShmoys_edge_ncard_mono

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_drawing_supergraph G hG
  exact ⟨H, hGH,
    WilliamsonShmoys.maximal_planar_drawing_connected H hH hmax,
    hH, WilliamsonShmoys.edge_ncard_mono G H hGH⟩