-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_cbce8d52_767a_43cf_a345_07ed3485307d
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:39:26.938702+00:00
-- url     : https://prove2.me/submissions/f102778a-b85b-4335-a76f-0fe009d3377b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_from_maximality

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ H' : SimpleGraph V,
      H ≤ H' → WilliamsonShmoys.HasPlanarDrawingOn H' → H' = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.maximal_planar_edge_upper_bound H hV hDraw
  have hLower := WilliamsonShmoys.maximal_planar_edge_lower_bound_from_maximality
    H hDraw hV hMax
  omega