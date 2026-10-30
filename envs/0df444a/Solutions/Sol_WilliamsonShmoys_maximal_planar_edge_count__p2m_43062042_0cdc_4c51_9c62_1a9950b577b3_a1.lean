-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_43062042_0cdc_4c51_9c62_1a9950b577b3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:30:52.664806+00:00
-- url     : https://prove2.me/submissions/4500076b-6ef0-4468-9b21-d9647152721d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_count_upper__p2m_a57dc3db_20ea_40d3_9b0f_dcd4c88e6cc2_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_edge_count_lower__p2m_a57dc3db_20ea_40d3_9b0f_dcd4c88e6cc2_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V, L <= M ->
      WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hCard : 3 <= Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_simple_graph_edge_count_upper__p2m_a57dc3db_20ea_40d3_9b0f_dcd4c88e6cc2_a1
    L hDraw hCard
  have hLower := WilliamsonShmoys.maximal_planar_simple_graph_edge_count_lower__p2m_a57dc3db_20ea_40d3_9b0f_dcd4c88e6cc2_a1
    L hDraw hMax hCard
  omega