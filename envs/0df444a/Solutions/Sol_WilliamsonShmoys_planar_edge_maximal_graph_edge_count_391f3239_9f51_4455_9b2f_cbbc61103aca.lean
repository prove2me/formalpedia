-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_maximal_graph_edge_count_391f3239_9f51_4455_9b2f_cbbc61103aca
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:51:24.791755+00:00
-- url     : https://prove2.me/submissions/44a2e0d5-4aad-4878-8d9c-ba8b76717bf7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_b65312a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_b65312a2
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : HasPlanarDrawingOn M)
    (hMmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_drawing_edge_upper_bound_b65312a2
    M hV hMdraw
  have hLower := WilliamsonShmoys.maximal_planar_edge_lower_bound_b65312a2
    M hV hMdraw hMmax
  omega