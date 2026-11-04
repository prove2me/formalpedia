-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_d07e54eb_c4bc_460d_b7df_6d44fa14b7ac_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:19:55.709452+00:00
-- url     : https://prove2.me/submissions/aef78a67-5d20-48ed-bbcf-e09449ee4acd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_upper_bound__p2m_267a842e_101e_4cf6_b705_d11d92433d33_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_lower_bound__p2m_267a842e_101e_4cf6_b705_d11d92433d33_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : 3 <= Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K = H) :
    (letI : DecidableRel H.Adj := dH;
     H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  letI : DecidableRel H.Adj := dH
  have hupper := WilliamsonShmoys.maximal_drawable_graph_edge_count_upper_bound__p2m_267a842e_101e_4cf6_b705_d11d92433d33_a1 H dH hH hn
  have hlower := WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound__p2m_267a842e_101e_4cf6_b705_d11d92433d33_a1 H dH hH hn hmax
  exact Nat.le_antisymm hupper hlower