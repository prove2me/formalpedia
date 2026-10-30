-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition_6009196b_f86b_4d84_8003_efa7e8eeee60
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:13:28.623605+00:00
-- url     : https://prove2.me/submissions/b4bc69e0-8253-41f4-854d-5fa178e42555

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_euler_face_count_for_edge_maximal_drawing

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  first
  | exact _root_.WilliamsonShmoys.exists_euler_face_count_for_edge_maximal_drawing
  | (apply _root_.WilliamsonShmoys.exists_euler_face_count_for_edge_maximal_drawing <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.exists_euler_face_count_for_edge_maximal_drawing <;> assumption)
