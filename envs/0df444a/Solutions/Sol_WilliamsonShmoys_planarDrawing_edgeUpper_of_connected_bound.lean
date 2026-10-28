-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_edgeUpper_of_connected_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:44:41.780915+00:00
-- url     : https://prove2.me/submissions/4054af86-5099-469a-9663-aea4d617dec8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_restrict_induced
import Theorems.Thm_WilliamsonShmoys_planarDrawing_edgeUpper_of_induced_bounds

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (connectedBound : ∀ {W : Type} [Fintype W] [LinearOrder W]
      (H : SimpleGraph W), H.Connected →
      WilliamsonShmoys.HasPlanarDrawingOn H →
      3 ≤ Fintype.card W →
      H.edgeSet.ncard + 6 ≤ 3 * Fintype.card W)
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  refine WilliamsonShmoys.planarDrawing_edgeUpper_of_induced_bounds
    G ?_ hV
  intro S hconn hS
  exact connectedBound (G.induce (↑S : Set V)) hconn
    (WilliamsonShmoys.planarDrawing_restrict_induced G hdraw S) hS