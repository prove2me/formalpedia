-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_edge_count__p2m_ba617e25_272f_480b_8c9f_e5a82d8e4502_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:56:37.654262+00:00
-- url     : https://prove2.me/submissions/7b1feb00-3694-491a-ac04-5bd6daf61c73

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_from_drawing__p2m_9b9fadfe_20c3_484e_b25c_37db0802734a_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound__p2m_9b9fadfe_20c3_484e_b25c_37db0802734a_a1

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V) (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S) :
    S.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound_from_drawing__p2m_9b9fadfe_20c3_484e_b25c_37db0802734a_a1 S hS hCard
  have hLower := WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_9b9fadfe_20c3_484e_b25c_37db0802734a_a1 S hS hCard hMax
  omega