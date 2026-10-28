-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawing_has_euler_face_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T21:54:23.60571+00:00
-- url     : https://prove2.me/submissions/e5e3264b-6b12-458c-9c53-c63ba6508759
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_relation
import Theorems.Thm_WilliamsonShmoys_connected_drawing_planar_edge_bound
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.connected_drawing_euler_relation G hconn hdraw
  have hedge := WilliamsonShmoys.connected_drawing_planar_edge_bound
    G hconn hdraw hcard
  refine ⟨f, heuler, ?_⟩
  omega