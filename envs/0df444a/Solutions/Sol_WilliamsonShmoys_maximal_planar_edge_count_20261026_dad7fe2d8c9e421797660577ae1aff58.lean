-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_20261026_dad7fe2d8c9e421797660577ae1aff58
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:31:25.956991+00:00
-- url     : https://prove2.me/submissions/d1df39b8-f3d7-46ea-b20d-868e868fd4bb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound_20261026_dad7fe2d8c9e421797660577ae1aff58
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_20261026_dad7fe2d8c9e421797660577ae1aff58

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall K' : SimpleGraph V, K <= K' ->
      WilliamsonShmoys.HasPlanarDrawingOn K' -> K' = K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.maximal_planar_edge_count_upper_bound_20261026_dad7fe2d8c9e421797660577ae1aff58 K hK hV
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_20261026_dad7fe2d8c9e421797660577ae1aff58 K hK hmax hV
  omega