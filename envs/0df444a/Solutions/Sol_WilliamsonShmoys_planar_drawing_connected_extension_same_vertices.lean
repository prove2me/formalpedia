-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_same_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:29:44.860203+00:00
-- url     : https://prove2.me/submissions/72dd3264-ebe3-4f0d-8469-ee0c1fa5b227

import Theorems.Thm_WilliamsonShmoys_connected_planar_augmentation

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        G.edgeSet.ncard ≤ H.edgeSet.ncard :=
  WilliamsonShmoys.connected_planar_augmentation G hV hG