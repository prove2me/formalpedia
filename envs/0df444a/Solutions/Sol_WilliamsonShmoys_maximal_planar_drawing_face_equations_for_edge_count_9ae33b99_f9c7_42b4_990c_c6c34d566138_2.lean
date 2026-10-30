-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_face_equations_for_edge_count_9ae33b99_f9c7_42b4_990c_c6c34d566138
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:14:16.987095+00:00
-- url     : https://prove2.me/submissions/4086b3c9-a4c6-4891-8e8c-9ee13e8f8ff0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_c4011bda_e2a2_4391_a47d_b4ea4febecd9

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  first
  | exact _root_.WilliamsonShmoys.maximal_planar_face_decomposition_c4011bda_e2a2_4391_a47d_b4ea4febecd9
  | (apply _root_.WilliamsonShmoys.maximal_planar_face_decomposition_c4011bda_e2a2_4391_a47d_b4ea4febecd9 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_planar_face_decomposition_c4011bda_e2a2_4391_a47d_b4ea4febecd9 <;> assumption)
