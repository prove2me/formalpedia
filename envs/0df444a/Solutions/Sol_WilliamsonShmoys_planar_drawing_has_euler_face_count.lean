-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_euler_face_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:54:03.529785+00:00
-- url     : https://prove2.me/submissions/c67c606a-10d5-411e-9772-ae458644671d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula
import Theorems.Thm_WilliamsonShmoys_planar_drawing_simple_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, G.edgeSet.ncard + 2 = Fintype.card V + f ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_formula
      G hConnected hDrawing
  have hEdge := WilliamsonShmoys.planar_drawing_simple_edge_bound
      G hConnected hDrawing hV
  refine ⟨f, hEuler, ?_⟩
  omega