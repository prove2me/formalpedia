-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_for_completion_437ae037_6315_4598_a71b_f3c87f44dd3b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:16:07.431132+00:00
-- url     : https://prove2.me/submissions/bbda278d-d79e-40cc-9ff5-97773ad1ca11

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_completion__p2m_437ae037_6315_4598_a71b_f3c87f44dd3b_a5

set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K →
      H.edgeSet ⊂ K.edgeSet → False)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.maximal_planar_drawing_edge_count_for_completion__p2m_437ae037_6315_4598_a71b_f3c87f44dd3b_a5
  | (apply _root_.WilliamsonShmoys.maximal_planar_drawing_edge_count_for_completion__p2m_437ae037_6315_4598_a71b_f3c87f44dd3b_a5 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_planar_drawing_edge_count_for_completion__p2m_437ae037_6315_4598_a71b_f3c87f44dd3b_a5 <;> assumption)
