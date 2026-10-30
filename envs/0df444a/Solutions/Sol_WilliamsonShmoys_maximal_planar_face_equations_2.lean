-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_face_equations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:14:51.623367+00:00
-- url     : https://prove2.me/submissions/6dc0a11d-2330-4c19-92fb-f98f018be613

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_euler_face_count_for_edge_maximal_drawing

set_option autoImplicit false

open WilliamsonShmoys
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
