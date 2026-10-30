-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_aea3a4e2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:14:36.366153+00:00
-- url     : https://prove2.me/submissions/7d52dc9d-3ecf-4d32-8238-bed5b8906a01

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_lower_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hKmax : ∀ L : SimpleGraph V, Set.Subset K.edgeSet L.edgeSet →
      HasPlanarDrawingOn L → Set.Subset L.edgeSet K.edgeSet) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.maximal_drawable_graph_edge_count_upper_bound K hV hK
  have hlower := WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound K hV hK hKmax
  omega