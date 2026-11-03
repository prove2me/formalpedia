-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_bounds__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:54:52.884883+00:00
-- url     : https://prove2.me/submissions/067c2b04-b4f8-4738-bcaa-a611b04a06f7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_subgraph_edge_card_le__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_connected__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1
import Theorems.Thm_WilliamsonShmoys_connected_edge_card_lower_bound__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_card_upper_bound__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hHK : H <= K)
    (hcard : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    And (H.edgeFinset.card <= K.edgeFinset.card)
      (And (Fintype.card V <= K.edgeFinset.card + 2)
        (K.edgeFinset.card <= 3 * Fintype.card V - 6)) := by
  apply And.intro
  · exact WilliamsonShmoys.subgraph_edge_card_le__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1 H K hHK
  · apply And.intro
    · have hconn :=
        WilliamsonShmoys.maximal_drawable_connected__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1
          K hcard hK hmax
      have htree :=
        WilliamsonShmoys.connected_edge_card_lower_bound__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1
          K hconn
      omega
    · exact WilliamsonShmoys.planar_edge_card_upper_bound__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1
        K hcard hK
