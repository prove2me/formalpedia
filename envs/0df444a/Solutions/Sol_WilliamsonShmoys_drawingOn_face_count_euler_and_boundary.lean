-- Prove2me | solution 1 for WilliamsonShmoys.drawingOn_face_count_euler_and_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:11:25.669909+00:00
-- url     : https://prove2.me/submissions/eb8e36f9-7e55-4a39-9818-488990ed5664

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawingOn_euler
import Theorems.Thm_WilliamsonShmoys_drawingOn_edge_bound

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.drawingOn_euler G hconn hdraw
  have hedge :=
    WilliamsonShmoys.drawingOn_edge_bound G hconn hdraw hcard
  refine ⟨f, heuler, ?_⟩
  omega