-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_of_connected_bound__p2m_49092f42_4606_480d_84ab_7522b76f4e32_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:45:12.912215+00:00
-- url     : https://prove2.me/submissions/12535fbb-8bf9-4fd5-b4e0-009195e5b80a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_connected__p2m_7cfe8adb_3896_4a89_9953_f0bd38318921_a1

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
    WilliamsonShmoys.planar_drawing_supergraph_connected__p2m_7cfe8adb_3896_4a89_9953_f0bd38318921_a1 X hX
  have hbound := hconn V Y hYconn hYdraw hV
  have hcard : X.edgeSet.ncard ≤ Y.edgeSet.ncard := Set.ncard_mono hXY
  omega