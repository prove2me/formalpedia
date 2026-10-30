-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_24bcd821_2a94_4cb2_b06f_eb5106ed464b
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:59:16.537452+00:00
-- url     : https://prove2.me/submissions/1311e4e8-eaa0-4134-99db-d2b94bfed317

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planarDrawingOn_edge_count_lower_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      M.edgeSet ⊂ N.edgeSet → ¬ HasPlanarDrawingOn N) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := planarDrawingOn_edge_count_upper_bound M hM hV
  have hLower := maximal_planarDrawingOn_edge_count_lower_bound M hM hV hMax
  omega