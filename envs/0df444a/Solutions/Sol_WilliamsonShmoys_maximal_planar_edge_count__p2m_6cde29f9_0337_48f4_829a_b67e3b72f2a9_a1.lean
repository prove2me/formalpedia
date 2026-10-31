-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_6cde29f9_0337_48f4_829a_b67e3b72f2a9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:22:15.909147+00:00
-- url     : https://prove2.me/submissions/d191b7b1-0ded-4a22-8f4f-f63b9dd16281

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_0869a5fc_4e7b_4b4a_9c67_2dc00ff9ed2f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_0869a5fc_4e7b_4b4a_9c67_2dc00ff9ed2f_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hU : HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V, U.edgeSet ⊆ W.edgeSet →
      HasPlanarDrawingOn W → U.edgeSet = W.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_0869a5fc_4e7b_4b4a_9c67_2dc00ff9ed2f_a1 U hU hV
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_0869a5fc_4e7b_4b4a_9c67_2dc00ff9ed2f_a1 U hU hmax hV
  omega