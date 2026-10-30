-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_22eb0949_0e91_449a_8343_64436b0a0efb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:05:59.462991+00:00
-- url     : https://prove2.me/submissions/1a025890-ac83-4cb5-ac02-b9223f8df651
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_76a86dc1_411a_4f86_8755_ab6ac02ce22d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_76a86dc1_411a_4f86_8755_ab6ac02ce22d_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    3 * Fintype.card V - 6 = T.edgeSet.ncard := by
  have hup := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_76a86dc1_411a_4f86_8755_ab6ac02ce22d_a1 T hV hT
  have hlo := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_76a86dc1_411a_4f86_8755_ab6ac02ce22d_a1 T hV hT hmax
  omega
