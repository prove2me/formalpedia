-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_maximal_supergraph_family__p2m_d834da15_b585_41bf_a8ee_e18eb971234e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:19:19.882572+00:00
-- url     : https://prove2.me/submissions/b893394a-dacb-4283-80fc-d982e1383acc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_feasible_supergraph_max_edge_count__p2m_116cb30c_31c6_4209_bff7_5b138df84190_a2
import Theorems.Thm_WilliamsonShmoys_graph_supergraph_subset_of_ncard_le__p2m_116cb30c_31c6_4209_bff7_5b138df84190_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (P : SimpleGraph V → Prop) (hM : P M) :
    ∃ T : SimpleGraph V,
      M.edgeSet.ncard ≤ T.edgeSet.ncard ∧
      M.edgeSet ⊆ T.edgeSet ∧
      P T ∧
      ∀ U : SimpleGraph V, T.edgeSet ⊆ U.edgeSet → P U →
        U.edgeSet ⊆ T.edgeSet := by
  obtain ⟨T, hcount, hMT, hPT, hmax⟩ :=
    WilliamsonShmoys.planarDrawingOn_feasible_supergraph_max_edge_count__p2m_116cb30c_31c6_4209_bff7_5b138df84190_a2
      M P hM
  refine ⟨T, hcount, hMT, hPT, ?_⟩
  intro U hTU hPU
  exact WilliamsonShmoys.graph_supergraph_subset_of_ncard_le__p2m_116cb30c_31c6_4209_bff7_5b138df84190_a2
    T U hTU (hmax U hTU hPU)