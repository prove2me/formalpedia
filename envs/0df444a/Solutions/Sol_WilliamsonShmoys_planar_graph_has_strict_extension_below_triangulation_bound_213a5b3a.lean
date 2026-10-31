-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_strict_extension_below_triangulation_bound_213a5b3a
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:48:34.902399+00:00
-- url     : https://prove2.me/submissions/30c2c05c-9f16-4d79-a94f-e4c241b8d47e

import Theorems.Thm_WilliamsonShmoys_planar_augmentation_when_sparse_v2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hE : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ J : SimpleGraph V, G ≤ J ∧ J ≠ G ∧
      WilliamsonShmoys.HasPlanarDrawingOn J :=
  WilliamsonShmoys.planar_augmentation_when_sparse_v2 G hV hG hE
