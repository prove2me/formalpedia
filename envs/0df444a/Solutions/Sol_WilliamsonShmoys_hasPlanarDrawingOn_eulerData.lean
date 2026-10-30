-- Prove2me | solution 1 for WilliamsonShmoys.hasPlanarDrawingOn_eulerData
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:20:59.450741+00:00
-- url     : https://prove2.me/submissions/2cbb0490-9bfb-447e-9fd1-47f6771503e6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarEulerData
import Theorems.Thm_WilliamsonShmoys_planarDrawing_edgeUpper
import Theorems.Thm_WilliamsonShmoys_connected_edgeLower

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) :
    Nonempty (WilliamsonShmoys.PlanarEulerData G) := by
  let v := Fintype.card V
  let e := G.edgeSet.ncard
  have hupper : e + 6 <= 3 * v :=
    WilliamsonShmoys.planarDrawing_edgeUpper G hdraw hV
  have hlower : v <= e + 1 :=
    WilliamsonShmoys.connected_edgeLower G hconn
  have hface : v <= e + 2 := by omega
  refine ⟨⟨Fin (e + 2 - v), inferInstance, ?_, ?_⟩⟩
  · simp only [Fintype.card_fin]
    simp only [v, e]
    omega
  · simp only [Fintype.card_fin]
    simp only [v, e]
    omega