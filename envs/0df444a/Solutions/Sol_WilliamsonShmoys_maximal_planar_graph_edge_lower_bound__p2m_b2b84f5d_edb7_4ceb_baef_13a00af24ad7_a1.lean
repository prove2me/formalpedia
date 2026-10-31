-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_b2b84f5d_edb7_4ceb_baef_13a00af24ad7_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:29:45.666016+00:00
-- url     : https://prove2.me/submissions/c1b5f149-c1e3-4ae0-9b12-579ee9a5fd80
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_4ab45211_21f9_4ad7_bbd8_2b8655cad493_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn R) (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ S : SimpleGraph V, R.edgeSet ⊆ S.edgeSet → HasPlanarDrawingOn S →
      S.edgeSet ⊆ R.edgeSet) :
    3 * Fintype.card V ≤ R.edgeSet.ncard + 6 := by
  exact WilliamsonShmoys.planar_drawing_edge_bound__p2m_4ab45211_21f9_4ad7_bbd8_2b8655cad493_a1 R hDraw