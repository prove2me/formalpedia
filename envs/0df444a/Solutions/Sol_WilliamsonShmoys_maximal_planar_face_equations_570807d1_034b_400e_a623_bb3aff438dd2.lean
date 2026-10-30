-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_equations_570807d1_034b_400e_a623_bb3aff438dd2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:39:50.872253+00:00
-- url     : https://prove2.me/submissions/fbb93987-04f7-434a-9c41-516bd2e46b45

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_for_edge_count_6274f47d_124c_4fd1_84e6_71540a951a1f

open WilliamsonShmoys

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  first
  | exact _root_.WilliamsonShmoys.maximal_planar_face_decomposition_for_edge_count_6274f47d_124c_4fd1_84e6_71540a951a1f
  | (apply _root_.WilliamsonShmoys.maximal_planar_face_decomposition_for_edge_count_6274f47d_124c_4fd1_84e6_71540a951a1f <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_planar_face_decomposition_for_edge_count_6274f47d_124c_4fd1_84e6_71540a951a1f <;> assumption)
