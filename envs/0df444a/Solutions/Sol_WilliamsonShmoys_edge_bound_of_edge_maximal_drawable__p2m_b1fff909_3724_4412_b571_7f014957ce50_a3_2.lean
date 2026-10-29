-- Prove2me | solution 2 for WilliamsonShmoys.edge_bound_of_edge_maximal_drawable__p2m_b1fff909_3724_4412_b571_7f014957ce50_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:48:52.918732+00:00
-- url     : https://prove2.me/submissions/5d3595a5-910f-416a-a337-a40d976b777d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet.ncard ≤ K.edgeSet.ncard) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  have hUpper := WilliamsonShmoys.planar_edge_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a2 K hDraw hCard
  have hLower := WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a2 K hDraw hCard hMax
  omega