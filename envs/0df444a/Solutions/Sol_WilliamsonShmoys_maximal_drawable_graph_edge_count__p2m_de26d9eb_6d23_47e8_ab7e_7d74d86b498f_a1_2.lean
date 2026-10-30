-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_de26d9eb_6d23_47e8_ab7e_7d74d86b498f_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:05:08.881548+00:00
-- url     : https://prove2.me/submissions/702994e8-339b-48b5-bd17-26142c5aef61

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_4b265a90_b8bd_4522_9040_b7d7632358e1_a1

open WilliamsonShmoys

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  first
  | exact _root_.WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4b265a90_b8bd_4522_9040_b7d7632358e1_a1
  | (apply _root_.WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4b265a90_b8bd_4522_9040_b7d7632358e1_a1 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4b265a90_b8bd_4522_9040_b7d7632358e1_a1 <;> assumption)
