-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_for_euler_counts_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:59:33.516552+00:00
-- url     : https://prove2.me/submissions/fadead40-7e60-4778-8fb3-4fdc72521117

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_for_edge_bound_v2
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_face_counts

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hConnected : L.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaceIncidence⟩ :=
    WilliamsonShmoys.planar_drawing_face_count_for_edge_bound_v2
      L hLdraw hConnected hCard
  exact WilliamsonShmoys.planar_edge_bound_from_face_counts
    (Fintype.card V) L.edgeSet.ncard f hEuler hFaceIncidence