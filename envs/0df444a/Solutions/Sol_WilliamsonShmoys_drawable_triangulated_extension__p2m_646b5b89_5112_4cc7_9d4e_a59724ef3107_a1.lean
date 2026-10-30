-- Prove2me | solution 1 for WilliamsonShmoys.drawable_triangulated_extension__p2m_646b5b89_5112_4cc7_9d4e_a59724ef3107_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:49:52.600444+00:00
-- url     : https://prove2.me/submissions/e1ec3711-e7ee-4ce7-a2ea-af4ae51ac8cc

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_drawable_supergraph__p2m_642d3dbe_c8d0_469e_ba26_5e9db8ed7bc7_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_642d3dbe_c8d0_469e_ba26_5e9db8ed7bc7_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ P : SimpleGraph V,
      N ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
        P.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨P, hNP, hPDraw, hMax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph__p2m_642d3dbe_c8d0_469e_ba26_5e9db8ed7bc7_a1
      N hDraw
  refine ⟨P, hNP, hPDraw, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_642d3dbe_c8d0_469e_ba26_5e9db8ed7bc7_a1
    P hPDraw hMax hCard