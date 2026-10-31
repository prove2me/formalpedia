-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_8874575c_8d28_40c2_984e_f8a2d2056536_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:44:56.449023+00:00
-- url     : https://prove2.me/submissions/4c7ddad8-058d-4b32-af22-73ed281ec611

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_50a29994_a325_484b_b52e_c568c6fdc691_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_50a29994_a325_484b_b52e_c568c6fdc691_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hMax : ∀ U : SimpleGraph V, T ≤ U →
      WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.planar_edge_count_upper_bound__p2m_50a29994_a325_484b_b52e_c568c6fdc691_a1
      T hV hDraw
  have hLower :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_50a29994_a325_484b_b52e_c568c6fdc691_a1
      T hV hDraw hMax
  omega