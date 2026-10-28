-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_simple_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:44:42.061998+00:00
-- url     : https://prove2.me/submissions/1980870c-59f5-4d99-a248-2021a6046ea4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_euler_face_count_for_drawing
import Theorems.Thm_WilliamsonShmoys_three_face_sides_for_drawing

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.euler_face_count_for_drawing G hG hConn
  have hFace :=
    WilliamsonShmoys.three_face_sides_for_drawing G hG hConn hCard f hEuler
  omega