-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_v2_aux
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:49:40.816588+00:00
-- url     : https://prove2.me/submissions/287907f4-af3c-4fa8-afa4-b01c5bb918d7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_v2_aux_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_v2_aux_lower_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ (X : SimpleGraph V), WilliamsonShmoys.HasPlanarDrawingOn X →
      (∀ {u v}, W.Adj u v → X.Adj u v) → X = W) :
    W.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.maximal_planar_edge_count_v2_aux_upper_bound
    W hdraw hV
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_v2_aux_lower_bound
    W hdraw hV hmax
  omega