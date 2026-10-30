-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_a9181169_d523_4da1_8834_b734217e5ad6
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:01:12.822215+00:00
-- url     : https://prove2.me/submissions/1038a24e-0e2b-49d8-a377-b8c2f4265b79

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_planar_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_maximal_lower_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V, HasPlanarDrawingOn U →
      (∀ u v, T.Adj u v → U.Adj u v) → U = T) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.maximal_planar_edge_count_planar_upper_bound T hT hCard
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_maximal_lower_bound T hT hCard hmax
  omega