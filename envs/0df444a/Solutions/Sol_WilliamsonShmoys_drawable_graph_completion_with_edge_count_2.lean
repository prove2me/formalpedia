-- Prove2me | solution 2 for WilliamsonShmoys.drawable_graph_completion_with_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:10:28.068839+00:00
-- url     : https://prove2.me/submissions/ffb6e138-9eed-4c37-a949-b9abd17b5d05

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_completion__p2m_953852c9_9877_4510_aaba_a6b57c23a189_a4

open WilliamsonShmoys

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.planar_drawing_euler_completion__p2m_953852c9_9877_4510_aaba_a6b57c23a189_a4
  | (apply _root_.WilliamsonShmoys.planar_drawing_euler_completion__p2m_953852c9_9877_4510_aaba_a6b57c23a189_a4 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_drawing_euler_completion__p2m_953852c9_9877_4510_aaba_a6b57c23a189_a4 <;> assumption)
