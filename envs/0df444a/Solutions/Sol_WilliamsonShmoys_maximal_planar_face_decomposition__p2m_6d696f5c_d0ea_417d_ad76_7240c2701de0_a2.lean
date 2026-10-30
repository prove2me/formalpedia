-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition__p2m_6d696f5c_d0ea_417d_ad76_7240c2701de0_a2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:03:15.948526+00:00
-- url     : https://prove2.me/submissions/0fb84d49-a500-4e8b-8c3e-5a8478a8b3fe

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_euler_face_count_for_edge_maximal_drawing

open WilliamsonShmoys

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  first
  | exact _root_.WilliamsonShmoys.exists_euler_face_count_for_edge_maximal_drawing
  | (apply _root_.WilliamsonShmoys.exists_euler_face_count_for_edge_maximal_drawing <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.exists_euler_face_count_for_edge_maximal_drawing <;> assumption)
