-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_triangulation_extension__p2m_059077c0_2625_4e05_919b_c819570c30dd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:50:15.559194+00:00
-- url     : https://prove2.me/submissions/4d41fb3c-65b9-42d7-8aaa-f40da39025e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_0edcc40e_6850_49bc_8dd7_6d053c5782bf_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_0edcc40e_6850_49bc_8dd7_6d053c5782bf_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V) (hCard : 3 <= Fintype.card V)
    (hS : HasPlanarDrawingOn S) :
    ∃ T : SimpleGraph V,
      (∀ u v, S.Adj u v → T.Adj u v) ∧
      HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hST, hT, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_0edcc40e_6850_49bc_8dd7_6d053c5782bf_a1
      S hS
  refine ⟨T, hST, hT, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_0edcc40e_6850_49bc_8dd7_6d053c5782bf_a1
    T hCard hT hMax
