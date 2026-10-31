-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_bound_of_connected_bound__p2m_49092f42_4606_480d_84ab_7522b76f4e32_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:31:53.359276+00:00
-- url     : https://prove2.me/submissions/06b307f6-8053-4a24-b913-ea8f3faf6a04

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_connected__p2m_7cfe8adb_3896_4a89_9953_f0bd38318921_a2

set_option autoImplicit false

theorem solution
    (hconn : ∀ (W : Type) [Fintype W] [LinearOrder W] (Y : SimpleGraph W),
      Y.Connected → WilliamsonShmoys.HasPlanarDrawingOn Y →
      3 ≤ Fintype.card W → Y.edgeSet.ncard + 6 ≤ 3 * Fintype.card W)
    {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hV : 3 ≤ Fintype.card V) :
    X.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨Y, hXY, hYconn, hYdraw⟩ :=
    WilliamsonShmoys.planar_drawing_supergraph_connected__p2m_7cfe8adb_3896_4a89_9953_f0bd38318921_a2
      X hX hV
  have hbound := hconn V Y hYconn hYdraw hV
  have hcard : X.edgeSet.ncard ≤ Y.edgeSet.ncard := Set.ncard_mono hXY
  omega