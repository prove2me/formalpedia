-- Prove2me | solution 2 for WilliamsonShmoys.planar_augmentation_to_triangulation_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:48:02.51108+00:00
-- url     : https://prove2.me/submissions/5e8989d7-d86c-4d26-9191-00afb4d4f149

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_edge_count_candidate

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  first
  | exact _root_.WilliamsonShmoys.planar_triangulation_completion_edge_count_candidate
  | (apply _root_.WilliamsonShmoys.planar_triangulation_completion_edge_count_candidate <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_triangulation_completion_edge_count_candidate <;> assumption)
