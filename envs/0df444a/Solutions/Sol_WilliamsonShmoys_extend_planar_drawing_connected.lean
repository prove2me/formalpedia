-- Prove2me | solution 1 for WilliamsonShmoys.extend_planar_drawing_connected
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:17:33.439978+00:00
-- url     : https://prove2.me/submissions/7638aa97-f6ec-4523-9036-f83d4c942634

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connectedification_retry3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H :=
  WilliamsonShmoys.planar_drawing_connectedification_retry3 G hdraw hV