-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_card_eq__p2m_aba97578_a55f_467d_b26f_e953a5f6767e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:41:50.955259+00:00
-- url     : https://prove2.me/submissions/b46cc0e1-ff95-4fec-b94a-2f4e72bf76dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_b387e51f_12e6_457e_b8c7_5aeeed4116ef_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_edge_lower_bound__p2m_b387e51f_12e6_457e_b8c7_5aeeed4116ef_a1
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_b387e51f_12e6_457e_b8c7_5aeeed4116ef_a1 H hV hH
  have hLower := WilliamsonShmoys.edge_maximal_planar_graph_edge_lower_bound__p2m_b387e51f_12e6_457e_b8c7_5aeeed4116ef_a1 H hV hH hMax
  omega
