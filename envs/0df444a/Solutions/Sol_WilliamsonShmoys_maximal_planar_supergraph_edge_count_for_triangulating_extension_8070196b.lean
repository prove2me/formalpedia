-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_count_for_triangulating_extension_8070196b
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:18:12.804283+00:00
-- url     : https://prove2.me/submissions/12250918-5e46-4f22-bf61-2f4c143ac364

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound_repair_053a8a16
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound_repair_053a8a16

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T)
    (hTU : T.edgeSet ⊆ U.edgeSet)
    (hU : HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V,
      U.edgeSet ⊆ W.edgeSet →
      HasPlanarDrawingOn W →
      W.edgeSet ⊆ U.edgeSet) :
    U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planar_simple_graph_edge_upper_bound_repair_053a8a16 U hV hU
  have hlower := WilliamsonShmoys.maximal_planar_graph_edge_lower_bound_repair_053a8a16 U hV hU hmax
  omega