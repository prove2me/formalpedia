-- Prove2me | solution 3 for WilliamsonShmoys.connected_planar_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:19:03.040241+00:00
-- url     : https://prove2.me/submissions/ed33384e-3582-41b8-91a8-34414e3f35db

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_with_edge_mono
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard :=
  WilliamsonShmoys.planar_drawing_connected_extension_with_edge_mono G hV hG
