-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_face_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:45:14.705263+00:00
-- url     : https://prove2.me/submissions/67bc04e8-375a-4281-bf14-9edfd4808448

import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_formula_bf226c5d
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_bf226c5d

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by
  obtain ⟨f, hf⟩ :=
    WilliamsonShmoys.connected_planar_drawing_euler_formula_bf226c5d G hConnected hG
  have he :=
    WilliamsonShmoys.planar_simple_edge_bound_bf226c5d G hV hG
  refine ⟨f, hf, ?_⟩
  omega