-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_accounting
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:46:52.492502+00:00
-- url     : https://prove2.me/submissions/52455065-ef97-4b99-af8e-3a2cbc75165d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_for_face_accounting_57972424
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_face_accounting_57972424

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V) :
    Exists (fun f : Nat => Exists (fun b : Nat =>
      Fintype.card V + f = G.edgeSet.ncard + 2 /\
      2 * G.edgeSet.ncard = b /\
      3 * f <= b)) := by
  obtain ⟨f, hEuler⟩ := WilliamsonShmoys.planar_drawing_euler_for_face_accounting_57972424 G hDraw hConn
  have hEdge := WilliamsonShmoys.planar_edge_bound_for_face_accounting_57972424 G hDraw hConn hCard
  refine ⟨f, 2 * G.edgeSet.ncard, hEuler, rfl, ?_⟩
  omega