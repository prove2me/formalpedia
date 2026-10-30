-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_face_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:26:31.351351+00:00
-- url     : https://prove2.me/submissions/23d4f397-0463-4e77-998e-f68f945ca92f

import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_from_embedding
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_from_embedding
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConn : G.Connected)
    (hGdraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      G.edgeSet.ncard + 2 = Fintype.card V + f ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.connected_planar_drawing_euler_from_embedding G hConn hGdraw
  have hEdge :=
    WilliamsonShmoys.connected_planar_drawing_edge_bound_from_embedding
      G hConn hGdraw hCard
  refine ⟨f, hEuler, ?_⟩
  omega