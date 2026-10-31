-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_26e2da54_dd0c_435f_9e8a_3d66581789dc_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:51:47.188521+00:00
-- url     : https://prove2.me/submissions/32dcbdce-b843-48e5-a7ec-4998c1649932
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_65576344_96ee_4070_89ba_6bada339cc97_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_65576344_96ee_4070_89ba_6bada339cc97_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V) (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ u v, Y.Adj u v → H.Adj u v) ∧
      Y.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hExt, hLarge, hH, hMax⟩ := WilliamsonShmoys.planar_drawing_maximal_extension__p2m_65576344_96ee_4070_89ba_6bada339cc97_a1 Y hY
  have hCount := WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_65576344_96ee_4070_89ba_6bada339cc97_a1 H hH hV hMax
  exact ⟨H, hExt, hLarge, hCount⟩