-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:53:02.30221+00:00
-- url     : https://prove2.me/submissions/67135f20-cd79-41a6-bd30-3555110402c4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_20261026
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_20261026

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, J ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = J) :
    J.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_edge_count_upper_bound_20261026 J hJ hV
  · exact WilliamsonShmoys.maximal_planar_edge_count_lower_bound_20261026
      J hJ hV hMax