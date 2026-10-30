-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_b9438800_deb6_4b0a_aabe_23abb7aa4f9e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:45:03.787467+00:00
-- url     : https://prove2.me/submissions/84ddcd18-54b5-43f6-b835-56c91db60348
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_878f63d5_f8a4_40b9_aba3_29559d5a92e2_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_878f63d5_f8a4_40b9_aba3_29559d5a92e2_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_878f63d5_f8a4_40b9_aba3_29559d5a92e2_a1 M hM hV
  have hlower := WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_878f63d5_f8a4_40b9_aba3_29559d5a92e2_a1 M hM hV hMax
  omega
