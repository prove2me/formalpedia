-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_on_card_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T19:08:38.571498+00:00
-- url     : https://prove2.me/submissions/ea53ea01-50bc-43ca-a8ca-933ec2e24fa6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_IsMaximalPlanarOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_drawing
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_for_drawing

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hKmax : IsMaximalPlanarOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound_for_drawing K hKmax.1 hV
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_for_drawing K hKmax hV
  omega