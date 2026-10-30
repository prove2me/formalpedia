-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_face_count_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:47:39.703051+00:00
-- url     : https://prove2.me/submissions/fae3e36d-ae11-4880-99dd-f6ea95b70bb8

import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_count_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConn : G.Connected)
    (hGdraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.connected_planar_drawing_euler_face_count_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
      G hConn hGdraw
  have hEdge := WilliamsonShmoys.connected_planar_drawing_edge_bound_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
      G hConn hGdraw hCard
  refine ⟨f, hEuler, ?_⟩
  omega