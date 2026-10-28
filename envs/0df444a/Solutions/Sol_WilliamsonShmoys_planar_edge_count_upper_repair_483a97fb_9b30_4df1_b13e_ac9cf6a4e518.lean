-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:21:13.902476+00:00
-- url     : https://prove2.me/submissions/23b49c3f-c4aa-436f-a0b0-987c71f8ed38
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_face_count_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, _hsub, hConn, hHdraw, hEdgeCount⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
      G hGdraw hCard
  obtain ⟨f, hEuler, hFaceBoundary⟩ :=
    WilliamsonShmoys.connected_planar_drawing_face_count_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
      H hConn hHdraw hCard
  omega