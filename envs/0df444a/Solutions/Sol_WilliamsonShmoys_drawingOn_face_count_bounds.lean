-- Prove2me | solution 1 for WilliamsonShmoys.drawingOn_face_count_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:38:41.515637+00:00
-- url     : https://prove2.me/submissions/e3f61d18-ae9b-4003-b401-2db93cb9a216

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawingOn_euler_face_count
import Theorems.Thm_WilliamsonShmoys_drawingOn_face_boundary_bound
set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : Nat, Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.drawingOn_euler_face_count G hconn hdraw hcard
  refine ⟨f, heuler, ?_⟩
  exact WilliamsonShmoys.drawingOn_face_boundary_bound
    G hconn hdraw hcard f heuler