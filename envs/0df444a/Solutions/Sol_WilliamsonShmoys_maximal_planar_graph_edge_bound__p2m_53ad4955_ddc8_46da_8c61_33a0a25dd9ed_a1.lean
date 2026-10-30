-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_53ad4955_ddc8_46da_8c61_33a0a25dd9ed_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:37:52.387456+00:00
-- url     : https://prove2.me/submissions/98455d84-b724-4166-b661-56a7b38a799c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_triangulation_extension__p2m_059077c0_2625_4e05_919b_c819570c30dd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_subgraph_edgeSet_eq__p2m_059077c0_2625_4e05_919b_c819570c30dd_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hS : HasPlanarDrawingOn S)
    (hMax : ∀ T : SimpleGraph V,
      (∀ u v, S.Adj u v → T.Adj u v) →
      HasPlanarDrawingOn T →
      ∀ u v, T.Adj u v → S.Adj u v) :
    3 * Fintype.card V - 6 <= S.edgeSet.ncard := by
  obtain ⟨ T, hST, hT, hCount ⟩ :=
    WilliamsonShmoys.maximal_planar_graph_triangulation_extension__p2m_059077c0_2625_4e05_919b_c819570c30dd_a1
      S hCard hS
  have hEq :=
    WilliamsonShmoys.maximal_drawable_subgraph_edgeSet_eq__p2m_059077c0_2625_4e05_919b_c819570c30dd_a1
      S T hST hT hMax
  rw [hEq, hCount]