-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_disconnected_extension_repair_3e188728
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:35:24.646906+00:00
-- url     : https://prove2.me/submissions/8b452191-3a0e-41d3-a13d-862c4e2b8d77
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_repair_3e188728
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_connected_repair_3e188728
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_mono_repair_3e188728

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : HasPlanarDrawingOn Y)
    (hV : 0 < Fintype.card V)
    (hDisconnected : ¬ Y.Connected) :
    ∃ H : SimpleGraph V,
      Y ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H ∧
      Y.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hYH, hH, hMaximal⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_repair_3e188728 Y hY hV
  have hConnected :=
    WilliamsonShmoys.planar_drawing_maximal_connected_repair_3e188728 H hH hV hMaximal
  have hCount :=
    WilliamsonShmoys.planar_drawing_edge_count_mono_repair_3e188728 Y H hYH
  exact ⟨H, hYH, hConnected, hH, hCount⟩