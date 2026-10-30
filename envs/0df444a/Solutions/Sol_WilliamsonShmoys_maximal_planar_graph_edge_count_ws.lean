-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_ws
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:38:32.445402+00:00
-- url     : https://prove2.me/submissions/93bb0b15-075e-4c76-bd66-36d4d79216d2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_ws
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_ws

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  have hlow := WilliamsonShmoys.maximal_planar_edge_lower_bound_ws M hM hcard hmax
  have hupp := WilliamsonShmoys.planar_edge_upper_bound_ws M hM hcard
  omega