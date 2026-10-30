-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:13:27.121063+00:00
-- url     : https://prove2.me/submissions/29cc3724-41e6-40ab-b863-14ebcaa7045f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_4b265a90_b8bd_4522_9040_b7d7632358e1_a1

set_option autoImplicit false
theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) : 3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  first
  | exact _root_.WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4b265a90_b8bd_4522_9040_b7d7632358e1_a1
  | (apply _root_.WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4b265a90_b8bd_4522_9040_b7d7632358e1_a1 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4b265a90_b8bd_4522_9040_b7d7632358e1_a1 <;> assumption)
