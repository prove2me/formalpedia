-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_count_bound_for_edge_count_bound_caf89453_fefb_49cf_ad04_ba4468da8e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:38:23.333273+00:00
-- url     : https://prove2.me/submissions/9a499976-557f-45be-b2ba-e6d4eff7fef2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_euler_face_count
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_face_degree_bound
set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected) (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  have hexists :=
    WilliamsonShmoys.connected_planar_drawing_edge_bound_euler_face_count
      G hG hConn
  cases hexists with
  | intro f heuler =>
      have hfaces :=
        WilliamsonShmoys.connected_planar_drawing_edge_bound_face_degree_bound
          G hG hConn hCard f heuler
      omega