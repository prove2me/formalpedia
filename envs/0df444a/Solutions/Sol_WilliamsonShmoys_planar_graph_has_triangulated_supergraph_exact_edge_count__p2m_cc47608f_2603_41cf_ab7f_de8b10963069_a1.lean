-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulated_supergraph_exact_edge_count__p2m_cc47608f_2603_41cf_ab7f_de8b10963069_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:59:58.631812+00:00
-- url     : https://prove2.me/submissions/790081b9-7bec-4f9b-afa9-b4554f7f9671
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_22eb0949_0e91_449a_8343_64436b0a0efb_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_22eb0949_0e91_449a_8343_64436b0a0efb_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V,
      L ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        3 * Fintype.card V - 6 = T.edgeSet.ncard := by
  obtain ⟨T, hLT, hT, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_22eb0949_0e91_449a_8343_64436b0a0efb_a1
      L hL
  have hedge :=
    WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_22eb0949_0e91_449a_8343_64436b0a0efb_a1
      T hV hT hmax
  exact ⟨T, hLT, hT, hedge⟩