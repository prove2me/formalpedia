-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_repair_3e188728
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:51:20.601161+00:00
-- url     : https://prove2.me/submissions/29dfbfc8-3761-4c39-815b-73f36cd20854
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_extension_repair_3e188728

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : HasPlanarDrawingOn Y)
    (hV : 0 < Fintype.card V) :
    ∃ H : SimpleGraph V,
      H.Connected ∧ HasPlanarDrawingOn H ∧
      Y.edgeSet.ncard ≤ H.edgeSet.ncard := by
  by_cases hconn : Y.Connected
  · exact ⟨Y, hconn, hY, le_rfl⟩
  · obtain ⟨H, _hYH, hHconn, hHplanar, hEdges⟩ :=
      WilliamsonShmoys.planar_drawing_disconnected_extension_repair_3e188728
        Y hY hV hconn
    exact ⟨H, hHconn, hHplanar, hEdges⟩