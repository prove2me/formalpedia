-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_aaf88115_3b68_495f_bd0f_37f00b1cdc73_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:37:12.378124+00:00
-- url     : https://prove2.me/submissions/977b1306-4054-4af2-af3e-2854974da1a5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_can_be_augmented_below_triangulation_bound__p2m_03ab0e36_fd73_4929_a651_a82d3a3cc822_a1
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound__p2m_03ab0e36_fd73_4929_a651_a82d3a3cc822_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hbound := WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_03ab0e36_fd73_4929_a651_a82d3a3cc822_a1 M hV hM
  by_contra hEq
  have hlt : M.edgeSet.ncard < 3 * Fintype.card V - 6 := by omega
  obtain ⟨N, hMN, hNe, hN⟩ := WilliamsonShmoys.planar_graph_can_be_augmented_below_triangulation_bound__p2m_03ab0e36_fd73_4929_a651_a82d3a3cc822_a1 M hV hM hlt
  exact hNe (hmax N hMN hN)