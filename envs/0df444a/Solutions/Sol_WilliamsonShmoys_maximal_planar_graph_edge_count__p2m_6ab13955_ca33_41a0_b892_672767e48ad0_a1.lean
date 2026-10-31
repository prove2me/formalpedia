-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_6ab13955_ca33_41a0_b892_672767e48ad0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:41:02.606979+00:00
-- url     : https://prove2.me/submissions/a0612d30-e1fe-4041-97d4-40f38abd2392

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_upper__p2m_19c9eeac_1bda_4675_8c1b_5590acff2ab1_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_lower__p2m_19c9eeac_1bda_4675_8c1b_5590acff2ab1_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn R) (hV : 3 <= Fintype.card V)
    (hmax : forall S : SimpleGraph V, R <= S -> HasPlanarDrawingOn S -> S = R) :
    R.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.maximal_planar_graph_edge_count_upper__p2m_19c9eeac_1bda_4675_8c1b_5590acff2ab1_a1 R hDraw hV
  have hlower := WilliamsonShmoys.maximal_planar_graph_edge_count_lower__p2m_19c9eeac_1bda_4675_8c1b_5590acff2ab1_a1 R hDraw hV hmax
  omega