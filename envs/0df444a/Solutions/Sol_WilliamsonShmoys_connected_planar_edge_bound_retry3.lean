-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound_retry3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:16:40.298647+00:00
-- url     : https://prove2.me/submissions/dc485fe7-6a1f-4986-a8e9-8a5a6ae85988
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_accounting
import Theorems.Thm_WilliamsonShmoys_face_accounting_implies_edge_bound
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, b, hEuler, hIncidences, hFaceLength⟩ :=
    WilliamsonShmoys.planar_drawing_face_accounting G hDraw hConn hCard
  exact WilliamsonShmoys.face_accounting_implies_edge_bound G
    ⟨f, b, hEuler, hIncidences, hFaceLength⟩