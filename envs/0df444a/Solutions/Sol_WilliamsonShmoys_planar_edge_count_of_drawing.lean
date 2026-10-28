-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_of_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:54:10.332578+00:00
-- url     : https://prove2.me/submissions/6d0d3117-c760-45ad-aaf7-78796c29c428
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_augmentation_v3
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_v3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hKH, hDraw, hConn, hEdges⟩ :=
    WilliamsonShmoys.planar_edge_count_augmentation_v3 K hV hK
  have hBound :=
    WilliamsonShmoys.connected_planar_edge_bound_v3 H hV hDraw hConn
  omega